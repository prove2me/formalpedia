-- Prove2me | Theorems.Thm_GaussOptCVQKD_keyRate_ge_gaussian
-- name    : GaussOptCVQKD.keyRate_ge_gaussian
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:01:33.195687+00:00
-- url     : https://prove2.me/theorems/ca19a664-ac7a-4627-bf77-fcf658b52eea
-- title:
--   p.3 — optimality of Gaussian collective attacks: $K_\beta(\rho_{AB})\ge K_\beta(\rho^G_{AB})$ for every state with covariance matrix $\gamma_{AB}$ (DR and RR)
-- statement:
--   Let Alice and Bob share a density $\rho_{AB}$ of finitely many bosonic modes (each owned by Alice or Bob) with finite second moments, first moments $d$ and covariance matrix $\gamma_{AB}$. Fix a reconciliation efficiency $\beta\in[0,1]$, a direction (direct or reverse reconciliation) and the measurements (homodyne $x$, homodyne $p$ or heterodyne) that Alice and Bob apply to all of their modes. Let
--   $$
--   K_\beta(\rho_{AB})=\beta\,S(a{:}b)-\chi_{aE},\qquad \chi_{aE}=S(\rho_{AB})-\int da\,p(a)\,S(\rho^a_B)
--   $$
--   (for reverse reconciliation, $a\leftrightarrow b$ and $A\leftrightarrow B$). Then:
--
--   1. the mutual information $S(a{:}b)$, the entropy $S(\rho_{AB})$ and the averaged conditional entropy of the key party's measurement are finite;
--   2. a Gaussian state with first moments $d$ and covariance $\gamma_{AB}$ exists;
--   3. every Gaussian state $\rho^G_{AB}$ with covariance matrix $\gamma_{AB}$ (whatever its first moments) satisfies
--   $$
--   K_\beta(\rho_{AB})\ \ge\ K_\beta(\rho^G_{AB}).
--   $$
--
--   So the key rate against the Gaussian collective attack determined by $\gamma_{AB}$ is a lower bound on the secret key rate for any collective attack, Gaussian or not. With $\beta=0$ this says that Eve's Holevo information $\chi_{aE}$ is maximized by Gaussian states (p.4).
--
--   **Formalization Note** Quadratures $x=(a+a^\dagger)/\sqrt2$, vacuum covariance $I$; entropies and mutual information in nats. Clause 1 applies to every state with finite second moments, including each $\rho^G_{AB}$, so the real-valued $K$ is the paper's $K$ on both sides.
--
--   Differences from the source:
--
--   - generalization: one mode per party ((6)), or N modes per party ((7)) → every finite mode set I with every owner map I → {Alice, Bob}; reason: N = 1 or N modes on each side is the special case of an owner map with one or N modes per party
--   - generalization: direct reconciliation with perfect efficiency, K = S(a:b) − S(a:E) ((6)) → both directions (DR, and RR with a ↔ b, A ↔ B, p.3) and every reconciliation efficiency β ∈ [0, 1] (K = βS(a:b) − S(a:E), (11), p.4); reason: the paper extends its claim to RR (p.3) and to (11) (p.4) in prose; β = 1 with DR is (6)
--   - reading: 'for all bipartite quantum states ρAB with covariance matrix γAB, one has K(ρAB) ≥ K(ρ^G_AB)', ρ^G_AB the Gaussian state with the same γAB → every density with finite second moments (CompleteMoments ρ d γ); existence of a Gaussian state with moments (d, γ), and the inequality for every Gaussian state with covariance γ, any first moments; reason: 'with covariance matrix γAB' requires finite second moments; the Gaussian state with given moments is unique, and p.1 says the first moments play no role
--   - reading: S(a:E), Eve's Holevo information, from her purification → χ_aE = S(ρ_AB) − ∫ p(a) S(ρ^a_B) da, computed from ρ_AB alone; reason: p.2 gives this formula and p.3 says K 'does not depend on the purification of ρAB'; milestone holevo_from_rhoAB states the identity for every purification
--   - reading: K 'depends on the choice of the measurement done by Alice and Bob (and on the sifting if any)' → one measurement choice per party, applied to all of its modes (homodyne x, homodyne p or heterodyne); sifting not modelled; reason: (7): 'Alice (Bob) do the same measurement on her (his) N modes'; a sifted rate is an average of per-basis rates K_xx, K_pp, each covered with the same Gaussian state
--   - encoding: entropies and mutual information as real numbers → in nats, valued in [0, ∞], with their finiteness concluded (clause 1) and K real; reason: same values; the conclusion makes the conversion to reals harmless
--   - encoding: quadratures x, p and the heterodyne outcome α → x = (a + a†)/√2, vacuum covariance I (Support50.P14); heterodyne outcome recorded as √2(Re α, Im α); outcome laws and conditional states characterized by characteristic functions; reason: Lean convention; mutual information and Holevo quantities are invariant under an invertible linear relabelling of outcomes
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, 'Optimality of Gaussian attacks', p.3 (claim after (10)); RR extension p.3; (11) p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_GaussOptCVQKD_MeasurementModel
import Definitions.Def_GaussOptCVQKD_KeyRate

open scoped ENNReal
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Support50.P14 (InterleavedQuadrature OscillatorCovariance CompleteMoments GaussianAt)

namespace GaussOptCVQKD

/-- **Optimality of Gaussian collective attacks**, García-Patrón, Cerf, *Unconditional optimality
of Gaussian attacks against continuous-variable QKD*, arXiv:quant-ph/0608032v1,
"Optimality of Gaussian attacks", p.3: "Thus, using Eq. (4), we have proved that for all
bipartite quantum states ρAB with covariance matrix γAB, one has K(ρAB) ≥ K(ρ^G_AB)", with the
RR extension of p.3 ("one simply needs to interchange a ↔ b and A ↔ B") and the reconciliation
efficiency β ∈ [0, 1] of (11), p.4 ("our conclusions remain unchanged").

For every reconciliation efficiency `0 ≤ β ≤ 1`, direction `r` (DR or RR), measurement choices
`mA`, `mB` (homodyne x, homodyne p or heterodyne, one per party), every finite mode set `I` with
owner map `owner : I → Fin 2` (`0` = Alice, `1` = Bob), and every density `ρ` on the Fock space
of `I` with finite second moments, first moments `d` and covariance matrix `γ`:
1. the mutual information `S(a:b)`, the entropy `S(ρ)` and the averaged conditional entropy
   `∫ p(a) S(ρ^a)` of the key party's measurement are finite;
2. a Gaussian state with first moments `d` and covariance `γ` exists;
3. every Gaussian state `ρ^G` with covariance `γ` (any first moments) has `K(ρ^G) ≤ K(ρ)`.

**Formalization Note** Vacuum covariance `I`, `x = (a + a†)/√2` (Support50.P14); entropies and
mutual information in nats; `K` is `keyRate` (purification-free Holevo term, p.2); the pieces
are `ℝ≥0∞`-valued and clause 1 makes the real-valued `K` the paper's `K` for `ρ` and for every
`ρ^G` (which also has finite second moments). -/
theorem keyRate_ge_gaussian (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (r : Reconciliation)
    (mA mB : Measurement) {I : Type} [Fintype I] (owner : I → Fin 2) (ρ : State (Occupation I))
    (d : InterleavedQuadrature I → ℝ) (γ : OscillatorCovariance I)
    (hρ : CompleteMoments ρ.coefficients d γ) :
    (mutualInfo owner ![mA, mB] ρ.coefficients < ⊤ ∧ extendedEntropyNats ρ.coefficients < ⊤ ∧
      holevoIntegral owner ![mA, mB] ρ.coefficients r.keyParty r.otherParty < ⊤) ∧
    (∃ ρG : State (Occupation I), GaussianAt ρG.coefficients d γ) ∧
    ∀ (ρG : State (Occupation I)) (dG : InterleavedQuadrature I → ℝ),
      GaussianAt ρG.coefficients dG γ →
      keyRate β r mA mB I owner ρG.coefficients ≤ keyRate β r mA mB I owner ρ.coefficients := by sorry

end GaussOptCVQKD
