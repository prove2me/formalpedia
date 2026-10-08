-- Prove2me | Theorems.Thm_HessianDamping_IGAHD_theorem_6
-- name    : HessianDamping.IGAHD.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:04.41317+00:00
-- url     : https://prove2.me/theorems/198e2dd4-7a30-4567-8824-c88646a7900d
-- title:
--   Theorem 6 — IGAHD rate and weighted gradient summability
-- statement:
--   Let $f$ be a convex differentiable function on a real Hilbert space, with an $L$-Lipschitz gradient and a minimizer $x^*$. Let $(x_k,y_k)$ follow IGAHD with $\alpha\ge3$, $s>0$, $s\le1/L$, and $0\le\beta<2\sqrt{s}$. Then $E_k$ is eventually nonincreasing and
--
--   $$f(x_k)-f(x^*)=O(k^{-2})\quad(k\to\infty).$$
--
--   If $\beta>0$, both weighted gradient series converge:
--
--   $$\sum_{k\ge0}k^2\|\nabla f(y_k)\|^2<\infty,\qquad\sum_{k\ge0}k^2\|\nabla f(x_k)\|^2<\infty.$$
--
--   The theorem provides the principal value and gradient estimates for the inertial gradient algorithm with Hessian damping.
--
--   **Formalization Note** The printed claim that $E_k$ is nonincreasing at every index is false: for $f(u)=u^2/2$, $L=s=1$, $\alpha=3$, $\beta=0$, $x_0=0$, $x_1=1$, one gets $E_1=0<E_2=1/8$. The proof supports eventual monotonicity, which is stated here. The minimizer, differentiability, and positive $L,s$ are explicit to reflect the source's intended domain.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 15, Theorem 6; pp. 16–18, proof

import Mathlib
import Definitions.Def_HessianDamping_IGAHD_Setting

namespace HessianDamping.IGAHD

/-- Theorem 6, p. 15. The printed monotonicity has a finite-index counterexample; the proof establishes its eventual form. -/
theorem theorem_6 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : H) (hxstar : ∀ z : H, f xstar ≤ f z)
    (α β s : ℝ) (hα : 3 ≤ α) (hs : 0 < s) (hsL : s ≤ 1 / L)
    (hβ0 : 0 ≤ β) (hβs : β < 2 * Real.sqrt s)
    (x y : ℕ → H) (hrun : IsIGAHDRun f α β s x y) :
    (∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k ≥ k₀,
      EK f α β s x xstar (k + 1) ≤ EK f α β s x xstar k) ∧
    (fun k : ℕ => f (x k) - f xstar) =O[Filter.atTop]
      (fun k : ℕ => 1 / (k : ℝ) ^ 2) ∧
    (0 < β →
      Summable (fun k : ℕ => (k : ℝ) ^ 2 * ‖gradient f (y k)‖ ^ 2) ∧
      Summable (fun k : ℕ => (k : ℝ) ^ 2 * ‖gradient f (x k)‖ ^ 2)) := by sorry
end HessianDamping.IGAHD
