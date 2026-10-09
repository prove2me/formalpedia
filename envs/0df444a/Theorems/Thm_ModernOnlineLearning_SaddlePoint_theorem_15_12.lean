-- Prove2me | Theorems.Thm_ModernOnlineLearning_SaddlePoint_theorem_15_12
-- name    : ModernOnlineLearning.SaddlePoint.theorem_15_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:45.381302+00:00
-- url     : https://prove2.me/theorems/59861d22-2f2a-4226-a916-541afceaca74
-- title:
--   Theorem 15.12, pp. 248–249 — player regrets bound the averaged duality gap
-- statement:
--   Let $X,Y$ be nonempty closed convex sets, and let $x_t\in X$, $y_t\in Y$ be the simultaneous outputs of Algorithm 15.1 for $t=1,\ldots,T$, where $T\ge1$. Player $X$ receives $\ell_t(x)=f(x,y_t)$ and player $Y$ receives $h_t(y)=-f(x_t,y)$. Their regret identities say, for $u\in X$ and $v\in Y$,
--   $$
--   \frac1T\sum_t f(x_t,y_t)-\frac1T\sum_t f(u,y_t)=\frac1T\sum_t[f(x_t,y_t)-f(u,y_t)],
--   $$
--   $$
--   \frac1T\sum_t f(x_t,v)-\frac1T\sum_t f(x_t,y_t)=\frac1T\sum_t[f(x_t,v)-f(x_t,y_t)].
--   $$
--   If $f$ is convex in its first argument and concave in its second, and $u_T'$ minimizes $f(\cdot,\bar y_T)$ while $v_T'$ maximizes $f(\bar x_T,\cdot)$ on their respective sets, then
--   $$
--   f(\bar x_T,v_T')-f(u_T',\bar y_T)\le\frac{\operatorname{Regret}^X_T(u_T')+\operatorname{Regret}^Y_T(v_T')}{T}.
--   $$
--   The inequality converts two online regret bounds into a bound on the attained duality gap.
--
--   **Formalization Note** The two regret expressions are expanded as finite sums. The attained extrema appear as point witnesses, and the average uses the book's one-based index.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 15.12, pp. 248–249

import Mathlib
import Definitions.Def_ModernOnlineLearning_SaddlePoint_Setting

set_option autoImplicit false

namespace ModernOnlineLearning.SaddlePoint

/-- Theorem 15.12, pp. 248–249: the two regret identities and the
online-to-saddle-point duality-gap inequality. -/
theorem theorem_15_12 {EX EY : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [FiniteDimensional ℝ EY]
    (X : Set EX) (Y : Set EY) (f : EX → EY → ℝ)
    (x : ℕ → EX) (y : ℕ → EY) (T : ℕ)
    (hT : 1 ≤ T) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXclosed : IsClosed X) (hYclosed : IsClosed Y)
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hx : ∀ t ∈ Finset.Icc 1 T, x t ∈ X)
    (hy : ∀ t ∈ Finset.Icc 1 T, y t ∈ Y)
    (hfx : ∀ v ∈ Y, ConvexOn ℝ X (fun w => f w v))
    (hfy : ∀ u ∈ X, ConcaveOn ℝ Y (f u))
    (xm : EX) (ym : EY)
    (hmin : IsMinOn X (fun w => f w (avg T y)) xm)
    (hmax : IsMaxOn Y (f (avg T x)) ym) :
    (∀ u ∈ X,
      (∑ t ∈ Finset.Icc 1 T, f (x t) (y t)) / T -
        (∑ t ∈ Finset.Icc 1 T, f u (y t)) / T =
        (∑ t ∈ Finset.Icc 1 T, (f (x t) (y t) - f u (y t))) / T) ∧
    (∀ v ∈ Y,
      (∑ t ∈ Finset.Icc 1 T, f (x t) v) / T -
        (∑ t ∈ Finset.Icc 1 T, f (x t) (y t)) / T =
        (∑ t ∈ Finset.Icc 1 T, (f (x t) v - f (x t) (y t))) / T) ∧
    (f (avg T x) ym - f xm (avg T y) ≤
      ((∑ t ∈ Finset.Icc 1 T, (f (x t) (y t) - f xm (y t))) +
        (∑ t ∈ Finset.Icc 1 T, (f (x t) ym - f (x t) (y t)))) / T) := by sorry

end ModernOnlineLearning.SaddlePoint
