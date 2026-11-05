-- Prove2me | Theorems.Thm_LockingAccInfo_lemma5_conditional_entropy_bound
-- name    : LockingAccInfo.lemma5_conditional_entropy_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:21.827966+00:00
-- url     : https://prove2.me/theorems/784ba658-7f2b-4ed6-a4d7-692a2470737a
-- title:
--   Lemma 5 — $H(V|Z)\ge\min_\sigma H(\mathcal N[\sigma])$ when $\rho_E$ is completely mixed
-- statement:
--   Let $\rho_{VE}=\sum_vP_V(v)|v\rangle\langle v|\otimes\rho_{E|V=v}$ be a {cq}-state on a finite-dimensional $E$ whose marginal $\rho_E$ is the completely mixed state $\mathrm{id}/\dim(E)$. Let $\mathcal N:=\{\dim(E)\cdot P_V(v)\cdot\rho_{E|V=v}\}_{v}$. Then $\mathcal N$ is a POVM, and for every POVM $M$ on $E$ with outcome $Z$,
--
--   $$
--   H(V|Z)\;\ge\;\min_{\sigma}H(\mathcal N[\sigma]),
--   $$
--
--   where $\sigma$ ranges over all states on $E$ and $H(\mathcal N[\sigma])$ is the entropy of the outcome of $\mathcal N$ applied to $\sigma$.
--
--   This reduces a bound over all measurements (arbitrarily many outcomes) to a bound over single states, which is how Lemma 2 is proved (its step (5)).
--
--   Differences from the source:
--   - encoding: {cq}-state on systems V, E; ρ_E the completely mixed state → a valid published CQData with finite V and finite E; ensembleMean E = (dim E)⁻¹ · id; reason: Lean convention; the same states
--   - encoding: some fixed POVM M applied to E → the published Measurement: a finite POVM with any number of outcomes; reason: the paper's proof indexes outcomes by z and takes min_z; finite-outcome POVMs are the standard reading in finite dimension
--   - encoding: min_σ H(𝒩[σ]) over all states σ on E → sInf of the set of values H(𝒩[σ]) over density matrices σ; reason: the set is nonempty and bounded below by 0, and the minimum is attained by compactness of the state space and continuity, so sInf is the min
--   - encoding: log (base implied by 1 + H(Y) = H(XY)) → Shannon entropy in bits (Real.logb 2, 0 log 0 = 0); reason: the paper's own convention; h(p) ≥ 1 − |2p − 1| and H(XY) = 1 + H(Y) hold only in base 2
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, Appendix, Lemma 5, p.4

import Mathlib
import Definitions.Def_LockingAccInfo_outcomeEntropy
import Definitions.Def_LockingAccInfo_conditionalEntropy
import Definitions.Def_LockingAccInfo_lemma5POVM
open QAlgorithms (IsPOVM IsDensityMatrix effectProb)
open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData accessibleInformation ensembleMean)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, Lemma 5, p.4: "Let ρVE be a
{cq}-state with the property that ρE is the completely mixed state on E. For some fixed POVM M
applied to E, let H(V|Z) be the entropy of V conditioned on the outcome Z. Then
H(V|Z) ≥ min_σ H(N[σ]) where σ ranges over all states on E and H(N[σ]) denotes the entropy of the
outcome when the POVM N := {dim(E) · PV(v) · ρE|V=v}v∈V is applied to σ." The proof's first
sentence, "ρE is the completely mixed state on E implies that N is a POVM", is the first clause.

**Formalization Note.** V and E are finite (`Fintype`), the {cq}-state is a valid published
`CQData` ensemble, and "ρE is the completely mixed state" is `ensembleMean E = (dim E)⁻¹ · id`.
The POVM M is the published `Measurement` with any finite number of outcomes. The minimum over
states is the infimum of the set of values `H(N[σ])` over density matrices σ; this set is nonempty
and bounded below by 0, and the infimum is attained by compactness, so it is the paper's min.
Entropies are in bits. -/
theorem lemma5_conditional_entropy_bound {V Q : Type} [Fintype V] [Fintype Q] [DecidableEq Q]
    (E : CQData V Q) (hE : E.Valid)
    (hmix : ensembleMean E = ((Fintype.card Q : ℂ))⁻¹ • (1 : Matrix Q Q ℂ))
    (M : Measurement Q) :
    IsPOVM (lemma5POVM E) ∧
    sInf {h : ℝ | ∃ σ : Matrix Q Q ℂ, IsDensityMatrix σ ∧ h = outcomeEntropy (lemma5POVM E) σ}
      ≤ conditionalEntropy E M := by sorry

end LockingAccInfo
