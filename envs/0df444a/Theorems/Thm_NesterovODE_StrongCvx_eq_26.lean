-- Prove2me | Theorems.Thm_NesterovODE_StrongCvx_eq_26
-- name    : NesterovODE.StrongCvx.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:54.322567+00:00
-- url     : https://prove2.me/theorems/1bd4a141-ebb1-4ec0-b3c4-a5bdff497332
-- title:
--   (26), p. 18 — energy estimate at the threshold time
-- statement:
--   Under the strongly convex and smooth assumptions of §4.3, with $\mu>0$, $2<\alpha\leq2r/3$, a minimizer $x^\star$, and a solution of (17), the energy at $t_\alpha$ satisfies the two estimates of (26), culminating in
--
--   $$E_8(t_\alpha;\alpha)\leq(r-1)^2t_\alpha^{\alpha-2}\|x_0-x^\star\|^2+\frac{(\alpha-2)^2(r-1)^2\|x_0-x^\star\|^2}{4\mu t_\alpha^{4-\alpha}}.$$
--
--   This controls the threshold energy entirely by the initial distance and the paper's parameters.
--
--   **Formalization Note** Positive $\mu$ and $\alpha>2$ ensure that the denominator involving $t_\alpha$ is nonzero. The initial energy bound uses the Theorem 5 energy, with no new numerical constant.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 18, (26)

import Mathlib
import Definitions.Def_NesterovODE_StrongCvx_Setting

namespace NesterovODE.StrongCvx

/-- Both estimates in equation (26) at the threshold time. -/
theorem eq_26 (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (L : NNReal) (r α mu : ℝ)
    (x₀ xstar : NesterovODE.WellPosed.E n) (X V : ℝ → NesterovODE.WellPosed.E n)
    (hL : 0 < L) (hmu : 0 < mu) (hf : InSMuL mu L f)
    (ha : 2 < α) (hr : α ≤ 2 * r / 3)
    (hmin : ∀ y, f xstar ≤ f y)
    (hX : IsSolution f r x₀ X V) :
    energy8 f r α xstar X V (tAlpha r α mu) ≤
      (tAlpha r α mu) ^ α * (f (X (tAlpha r α mu)) - f xstar) +
      ((2 * r - α) ^ 2 * (tAlpha r α mu) ^ (α - 2) / 4) *
        ‖((2 * r - 2) / (2 * r - α)) • X (tAlpha r α mu) +
          (2 * (tAlpha r α mu) / (2 * r - α)) • V (tAlpha r α mu) -
          ((2 * r - 2) / (2 * r - α)) • xstar‖ ^ 2 +
      ((2 * r - α) ^ 2 * (tAlpha r α mu) ^ (α - 2) / 4) *
        ‖((α - 2) / (2 * r - α)) • X (tAlpha r α mu) -
          ((α - 2) / (2 * r - α)) • xstar‖ ^ 2 ∧
    energy8 f r α xstar X V (tAlpha r α mu) ≤
      (r - 1) ^ 2 * (tAlpha r α mu) ^ (α - 2) * ‖x₀ - xstar‖ ^ 2 +
      (α - 2) ^ 2 * (r - 1) ^ 2 * ‖x₀ - xstar‖ ^ 2 /
        (4 * mu * (tAlpha r α mu) ^ (4 - α)) := by sorry

end NesterovODE.StrongCvx
