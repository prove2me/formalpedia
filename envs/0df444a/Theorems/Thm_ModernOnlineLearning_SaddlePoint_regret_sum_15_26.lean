-- Prove2me | Theorems.Thm_ModernOnlineLearning_SaddlePoint_regret_sum_15_26
-- name    : ModernOnlineLearning.SaddlePoint.regret_sum_15_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:35.218068+00:00
-- url     : https://prove2.me/theorems/b1ecfa61-bc90-43cd-918a-1a4f28079895
-- title:
--   §15.5, p. 262 — summed player regrets with smoothness coefficients
-- statement:
--   Let both players run Algorithm 15.6 on nonempty closed convex sets $X,Y$. Assume $f$ is convex in $x$ and concave in $y$, its partial gradients satisfy (15.7)–(15.10), and the regularizers are respectively $\lambda_X$- and $\lambda_Y$-strongly convex, with positive parameters. For every $u\in X$ and $v\in Y$,
--   $$
--   \begin{aligned}
--   \sum_{t=1}^T[f(x_t,v)-f(u,y_t)]\le {}&\psi_X(u)-\psi_X(x_1)+\psi_Y(v)-\psi_Y(y_1)
--   +\frac{\|g_{X,1}\|_{X,*}^2}{\lambda_X}+\frac{\|g_{Y,1}\|_{Y,*}^2}{\lambda_Y}\\
--   &+\sum_{t=2}^T\left(\frac{2L_{XX}^2}{\lambda_X}+\frac{2L_{XY}^2}{\lambda_Y}-\frac{\lambda_X}{4}\right)\|x_t-x_{t-1}\|_X^2\\
--   &+\sum_{t=2}^T\left(\frac{2L_{YY}^2}{\lambda_Y}+\frac{2L_{XY}^2}{\lambda_X}-\frac{\lambda_Y}{4}\right)\|y_t-y_{t-1}\|_Y^2.
--   \end{aligned}
--   $$
--   This is the intermediate estimate immediately preceding Theorem 15.26; its two stability coefficients determine the theorem's required lower bounds on $\lambda_X$ and $\lambda_Y$.
--
--   **Formalization Note** The dual norms are operator norms. The sequence starts at round one, and the stability sums start at round two. The run is constrained only on rounds $1,\ldots,T$; the statement involves no iterate after $T$.
-- source:
--   Orabona, arXiv:1912.13213v10, §15.5, summed-regret display before Theorem 15.26, p. 262

import Mathlib
import Definitions.Def_ModernOnlineLearning_SaddlePoint_Setting

set_option autoImplicit false

namespace ModernOnlineLearning.SaddlePoint

/-- The summed-regret display in §15.5, p. 262, immediately before Theorem 15.26. -/
theorem regret_sum_15_26 {EX EY : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [FiniteDimensional ℝ EY]
    (X : Set EX) (Y : Set EY) (f : EX → EY → ℝ)
    (gx : EX → EY → EX →L[ℝ] ℝ) (gy : EX → EY → EY →L[ℝ] ℝ)
    (ψX : EX → ℝ) (ψY : EY → ℝ) (x : ℕ → EX) (y : ℕ → EY)
    (LXX LXY LYY lamX lamY : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXclosed : IsClosed X) (hYclosed : IsClosed Y)
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hfx : ∀ v ∈ Y, ConvexOn ℝ X (fun w => f w v))
    (hfy : ∀ u ∈ X, ConcaveOn ℝ Y (f u))
    (hLXX : 0 ≤ LXX) (hLXY : 0 ≤ LXY) (hLYY : 0 ≤ LYY)
    (hlamX : 0 < lamX) (hlamY : 0 < lamY)
    (hψX : StrongConvexOn X lamX ψX) (hψY : StrongConvexOn Y lamY ψY)
    (hsmooth : IsSmoothSaddleOn X Y f gx gy LXX LXY LYY)
    (hrun : IsOptFTRLSaddleRun X Y ψX ψY gx gy x y T) :
    ∀ u ∈ X, ∀ v ∈ Y,
      (∑ t ∈ Finset.Icc 1 T, (f (x t) v - f u (y t))) ≤
      ψX u - ψX (x 1) + ψY v - ψY (y 1) +
      ‖gx (x 1) (y 1)‖ ^ 2 / lamX + ‖gy (x 1) (y 1)‖ ^ 2 / lamY +
      (∑ t ∈ Finset.Icc 2 T,
        ((2 * LXX ^ 2 / lamX + 2 * LXY ^ 2 / lamY - lamX / 4) *
          ‖x t - x (t - 1)‖ ^ 2)) +
      (∑ t ∈ Finset.Icc 2 T,
        ((2 * LYY ^ 2 / lamY + 2 * LXY ^ 2 / lamX - lamY / 4) *
          ‖y t - y (t - 1)‖ ^ 2)) := by sorry

end ModernOnlineLearning.SaddlePoint
