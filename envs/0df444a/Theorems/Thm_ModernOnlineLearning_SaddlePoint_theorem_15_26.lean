-- Prove2me | Theorems.Thm_ModernOnlineLearning_SaddlePoint_theorem_15_26
-- name    : ModernOnlineLearning.SaddlePoint.theorem_15_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:33.673012+00:00
-- url     : https://prove2.me/theorems/768dd935-1a0c-4862-b2ac-68f67a13d56a
-- title:
--   Theorem 15.26, p. 263 — optimistic FTRL self-play has a constant-over-T duality-gap bound
-- statement:
--   Let $X,Y$ be nonempty closed convex feasible sets in two real normed spaces. Let $f:X\times Y\to\mathbb R$ be convex in its first argument, concave in its second, and smooth as in (15.7)–(15.10) with nonnegative constants $L_{XX},L_{XY},L_{YY}$. Run Algorithm 15.6 with $\lambda_X$-strongly convex regularizer $\psi_X$ and $\lambda_Y$-strongly convex regularizer $\psi_Y$. Assume $\alpha,\lambda_X,\lambda_Y>0$ and
--   $$
--   \lambda_X\ge2\sqrt2(L_{XX}+L_{XY}\alpha),\qquad
--   \lambda_Y\ge2\sqrt2(L_{YY}+L_{XY}/\alpha).
--   $$
--   For $T\ge1$, let $x_T'$ minimize $f(\cdot,\bar y_T)$ over $X$ and let $y_T'$ maximize $f(\bar x_T,\cdot)$ over $Y$. Then
--   $$
--   f(\bar x_T,y_T')-f(x_T',\bar y_T)\le
--   \frac{\psi_X(x_T')-\psi_X(x_1)+\psi_Y(y_T')-\psi_Y(y_1)+\|g_{X,1}\|_{X,*}^2/\lambda_X+\|g_{Y,1}\|_{Y,*}^2/\lambda_Y}{T}.
--   $$
--   The result gives the printed convergence certificate for the averages of optimistic FTRL self-play.
--
--   **Formalization Note** Gradients are continuous linear functionals on the ambient normed spaces, and their operator norms are the dual norms. The partial derivatives are supplied on an open neighborhood of $X\times Y$. The two attained extrema are given as arbitrary witnesses. Positivity of $T$ and the regularizer parameters rules out division by zero. The smoothness constants are explicitly nonnegative, as implicit in their use as Lipschitz constants. The run predicate enforces both argmin updates and the initial zero hints.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 15.26, p. 263; Algorithm 15.6 and (15.7)–(15.10), p. 261

import Mathlib
import Definitions.Def_ModernOnlineLearning_SaddlePoint_Setting

set_option autoImplicit false

namespace ModernOnlineLearning.SaddlePoint

/-- Theorem 15.26, p. 263: optimistic FTRL self-play has the printed
constant-over-T bound on the attained duality gap. -/
theorem theorem_15_26 {EX EY : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [FiniteDimensional ℝ EY]
    (X : Set EX) (Y : Set EY) (f : EX → EY → ℝ)
    (gx : EX → EY → EX →L[ℝ] ℝ) (gy : EX → EY → EY →L[ℝ] ℝ)
    (ψX : EX → ℝ) (ψY : EY → ℝ) (x : ℕ → EX) (y : ℕ → EY)
    (LXX LXY LYY lamX lamY alpha : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXclosed : IsClosed X) (hYclosed : IsClosed Y)
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hfx : ∀ v ∈ Y, ConvexOn ℝ X (fun w => f w v))
    (hfy : ∀ u ∈ X, ConcaveOn ℝ Y (f u))
    (hLXX : 0 ≤ LXX) (hLXY : 0 ≤ LXY) (hLYY : 0 ≤ LYY)
    (halpha : 0 < alpha) (hlamX : 0 < lamX) (hlamY : 0 < lamY)
    (hlowerX : 2 * Real.sqrt 2 * (LXX + LXY * alpha) ≤ lamX)
    (hlowerY : 2 * Real.sqrt 2 * (LYY + LXY / alpha) ≤ lamY)
    (hψX : StrongConvexOn X lamX ψX) (hψY : StrongConvexOn Y lamY ψY)
    (hsmooth : IsSmoothSaddleOn X Y f gx gy LXX LXY LYY)
    (hrun : IsOptFTRLSaddleRun X Y ψX ψY gx gy x y T)
    (xm : EX) (ym : EY)
    (hmin : IsMinOn X (fun w => f w (avg T y)) xm)
    (hmax : IsMaxOn Y (f (avg T x)) ym) :
    f (avg T x) ym - f xm (avg T y) ≤
      (ψX xm - ψX (x 1) + ψY ym - ψY (y 1) +
        ‖gx (x 1) (y 1)‖ ^ 2 / lamX +
        ‖gy (x 1) (y 1)‖ ^ 2 / lamY) / T := by sorry

end ModernOnlineLearning.SaddlePoint
