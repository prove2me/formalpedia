-- Prove2me | Theorems.Thm_HessianDamping_IGAHD_eps_ineq
-- name    : HessianDamping.IGAHD.eps_ineq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:54.690842+00:00
-- url     : https://prove2.me/theorems/8904c73b-47f0-41de-bbc9-04a3bd1bccf7
-- title:
--   §3.2, p. 18 — eventual epsilon energy inequality
-- statement:
--   Assume the hypotheses of Theorem 6 and $\beta>0$. For every $\varepsilon$ with $0<\varepsilon<2\beta\sqrt{s}-\beta^2$, there is an index $k_0$ such that for all $k\ge k_0$,
--
--   $$E_{k+1}-E_k+\frac{\varepsilon}{2}t_{k+1}^2\|\nabla f(y_k)\|^2\le0.$$
--
--   This is the paper's quantitative tail estimate for gradient summability.
--
--   **Formalization Note** The source says the preceding sign condition holds “for $k$ large enough”; the existential threshold makes that qualification explicit.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 18, proof of Theorem 6, epsilon inequality

import Mathlib
import Definitions.Def_HessianDamping_IGAHD_Setting

namespace HessianDamping.IGAHD

/-- The eventual ε-inequality in the proof of Theorem 6, p. 18. -/
theorem eps_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : H) (hxstar : ∀ z : H, f xstar ≤ f z)
    (α β s : ℝ) (hα : 3 ≤ α) (hs : 0 < s) (hsL : s ≤ 1 / L)
    (hβ0 : 0 ≤ β) (hβs : β < 2 * Real.sqrt s)
    (x y : ℕ → H) (hrun : IsIGAHDRun f α β s x y)
    (hβ : 0 < β) (ε : ℝ) (hε0 : 0 < ε)
    (hε : ε < 2 * Real.sqrt s * β - β ^ 2) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k ≥ k₀,
      EK f α β s x xstar (k + 1) - EK f α β s x xstar k
        + 1 / 2 * ε * tK α (k + 1) ^ 2 * ‖gradient f (y k)‖ ^ 2 ≤ 0 := by sorry
end HessianDamping.IGAHD
