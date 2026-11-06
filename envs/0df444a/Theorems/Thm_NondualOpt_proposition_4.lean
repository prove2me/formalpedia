-- Prove2me | Theorems.Thm_NondualOpt_proposition_4
-- name    : NondualOpt.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:03:42.579848+00:00
-- url     : https://prove2.me/theorems/eee0e23a-a1c9-4f6d-8385-9caf97a4bfab
-- title:
--   Proposition 4 — online reduction
-- statement:
--   Under Assumption 3, let $r_t(\cdot\mid\ell_{1:t-1})$ range over predictable laws on the admissible affine losses and let
--   $$
--   m_t(u)=\int\ell(u)\,r_t(d\ell\mid\ell_{1:t-1})
--   $$
--   be the conditional mean loss. Then
--   $$
--   V^{\max}_{X,H,T}\le\Big\langle\!\Big\langle\sup_{r_t}\mathbb E_{\ell_t\sim r_t}\Big\rangle\!\Big\rangle_{t=1}^T\ \sup_{u\in X}\Big\{\sum_{t=1}^Tm_t(u)-T\max_{t\le T}\ell_t(u)\Big\}.
--   $$
--   The player's choices are removed: the value is bounded by an adversary-only process comparing the mean of the conditional means with the maximum of the sampled losses. Combined with the affine structure of the losses this gives (10), the input of Lemma 5.
--
--   Differences from the source:
--   - generalization: E a real Banach space, H ⊆ E∗ bounded with the duality pairing, X closed and bounded with 0 ∈ X (§2 standing setting) → real vector spaces E, F with an abstract bilinear pairing, Λ_{X,H} < ∞, no closedness or boundedness of X and no 0 ∈ X; reason: the proofs use H only through pairings ⟨g, u⟩ and the bound Λ_{X,H} (footnote 7); the duality pairing between E∗ and E with bounded H is the instance F = E∗
--   - reading: the distributions r_t, s_t of ① in Assumption 3, with the measurable η-minimizer clause → finitely supported laws; the selection clause is not stated; reason: footnote 6, p.9: finitely supported adversarial laws suffice for the minimax interchanges; for such laws expectations are finite sums and the selection clause is automatic
--   - encoding: the supremum over adaptive strategies r_t → for every ε > 0 some adaptive adversary π attains the bound up to ε; reason: the supremum without a junk value over the strategy space
--   - encoding: losses ℓ_t ∈ F and their laws → loss indices z_t = (g_t, b_t) ∈ Z_{X,H} with ℓ_t = ⟨g_t, ·⟩ + b_t; extended-real values; T ≥ 1; reason: F is parameterized by Z_{X,H}; the payoff depends on z_t only through the loss, so at each stage of the nested supremum the best continuation after a history of indices is a function of the loss history, and adversaries reading indices attain the same value as adversaries reading losses
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Proposition 4, (9), p.10

import Mathlib
import Definitions.Def_NondualOpt_affineZ
import Definitions.Def_NondualOpt_affLoss
import Definitions.Def_NondualOpt_Vmax
import Definitions.Def_NondualOpt_Assumption3
import Definitions.Def_NondualOpt_FinLaw_mean
import Definitions.Def_NondualOpt_pathExpect
import Definitions.Def_NondualOpt_histPrefix

namespace NondualOpt

/-- **Proposition 4 (Online reduction).** Under Assumption 3, with predictable laws
`r_t(· | ℓ_{1:t−1})` on the admissible losses and `m_t(u) = ∫ ℓ(u) r_t(dℓ | ℓ_{1:t−1})`,
`V^max_{X,H,T} ≤ ⟪sup_{r_t} E_{ℓ_t ∼ r_t}⟫_{t=1}^T sup_{u ∈ X} {∑_t m_t(u) − T max_{t ≤ T} ℓ_t(u)}`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Proposition 4, (9), p.10.

**Formalization Note.** The supremum over adaptive adversaries is written `∀ ε > 0, ∃ π`. An
adversary `π t h` is a finitely supported law on `Z_{X,H}` given the loss history `h` (footnote 6,
p.9); `pathExpect` is the nested expectation over the path `z_{1:T}`. Losses are `affLoss pair z`,
and `m_t(u)` is the mean of `affLoss pair · u` under `π t (z_{<t})`. `EReal`-valued. -/
theorem proposition_4 {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F) (T : ℕ) (hT : 1 ≤ T)
    (hA : Assumption3 pair X H T) :
    ∀ ε : ℝ, 0 < ε → ∃ π : (t : ℕ) → (Fin t → F × ℝ) → FinLaw (affineZ pair X H),
      Vmax pair X H T - (ε : EReal) ≤
        pathExpect π (fun n z => ⨆ u : X,
          (((∑ t : Fin n, (π t (histPrefix z t)).mean (fun z' => affLoss pair z' u)) -
            (n : ℝ) * ⨆ t : Fin n, affLoss pair (z t) u : ℝ) : EReal)) T 0 Fin.elim0 := by sorry

end NondualOpt
