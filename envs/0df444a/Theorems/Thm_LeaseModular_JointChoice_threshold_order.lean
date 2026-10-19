-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_threshold_order
-- name    : LeaseModular.JointChoice.threshold_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:05.276986+00:00
-- url     : https://prove2.me/theorems/83ca52ca-a5a8-4017-a6d2-df717a2e9572
-- title:
--   Proof of Proposition 3, p. 36 — for γ ≤ 1, C_M < C_I < C_SM ≤ C_LM2, with C_SM < C_LM2 for γ < 1
-- statement:
--   Let $0<\delta_2<\delta_1<1$ and $0<\gamma\le1$. Then the cost thresholds satisfy
--   $$C_M(\delta_1,\delta_2,\gamma)<C_I(\delta_1,\delta_2,\gamma)<C_{SM}(\delta_1,\delta_2)\le C_{LM2}(\delta_1,\delta_2,\gamma),$$
--   and the last inequality is strict when $\gamma<1$.
--
--   This ordering is what turns the pairwise comparisons of Lemmas 1–3 into the three cost regions of Proposition 3.
--
--   **Formalization Note.** $C_{LM2}$ is the corrected threshold. At $\gamma=1$, $C_{SM}=C_{LM2}$ exactly, so the paper's strict "$C_{SM}<C_{LM2}$" is stated as "$\le$" for $\gamma\le1$ and as "$<$" for $\gamma<1$. Only the parameter inequalities the threshold formulas need are assumed.
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), proof of Proposition 3, Appendix p. 36

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Proof of Proposition 3, p. 36: for `0 < δ₂ < δ₁ < 1` and `0 < γ ≤ 1`,
`C_M < C_I < C_SM ≤ C_LM2` (with `C_LM2` corrected), and `C_SM < C_LM2` when `γ < 1`.
At `γ = 1`, `C_SM = C_LM2`. -/
theorem threshold_order (δ₁ δ₂ γ : ℝ) (h₂ : 0 < δ₂) (h₂₁ : δ₂ < δ₁) (h₁ : δ₁ < 1)
    (hγ₀ : 0 < γ) (hγ : γ ≤ 1) :
    CM δ₁ δ₂ γ < CI δ₁ δ₂ γ ∧ CI δ₁ δ₂ γ < CSM δ₁ δ₂ ∧ CSM δ₁ δ₂ ≤ CLM2 δ₁ δ₂ γ ∧
      (γ < 1 → CSM δ₁ δ₂ < CLM2 δ₁ δ₂ γ) := by sorry

end LeaseModular.JointChoice
