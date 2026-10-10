-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_cancelled_hessian_annulus_identity
-- name    : HunterPDE.Newtonian.cancelled_hessian_annulus_identity
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-10T10:31:55.611514+00:00
-- url     : https://prove2.me/theorems/648fbba6-c1c9-4d48-8d9c-5d3457c0eb01
-- title:
--   Finite-annulus integration by parts for the cancelled Newtonian Hessian
-- statement:
--   Let $n\ge2$, let $f\in C_c^2(\mathbb R^n)$, and suppose its support is contained in $B_R(x)$, where $0<r<R$. Write $\Gamma$ for the Newtonian fundamental solution, $A=B_R(x)\setminus\overline B_r(x)$ and
--
--   $$B_{ij}(R)=R^{n-1}\int_{S^{n-1}}\partial_i\Gamma(-R\omega)\omega_j\,dS(\omega).$$
--
--   For coordinate indices $i,j$, define the inner error
--
--   $$E_{ij}(r)=r^{n-1}\int_{S^{n-1}}\left[\Gamma(-r\omega)\partial_jf(x+r\omega)\omega_i+\partial_i\Gamma(-r\omega)(f(x+r\omega)-f(x))\omega_j\right]dS(\omega).$$
--
--   Then the exact finite-radius identity is
--
--   $$\int_A\partial_{ij}\Gamma(x-y)(f(y)-f(x))\,dy=\int_A\Gamma(x-y)\partial_{ij}f(y)\,dy+f(x)B_{ij}(R)+E_{ij}(r).$$
--
--   This separates integration by parts on a regular annulus from the estimates at the singularity, and applies at every positive inner radius below the outer radius.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed pp. 37–38, Eqs. (2.27)–(2.28) and subsequent inner-boundary estimates; finite-radius identity and quantitative C1 formulation.

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
open MeasureTheory HunterPDE.Newtonian Filter
open scoped ContDiff Topology

theorem HunterPDE.Newtonian.cancelled_hessian_annulus_identity
    (n : ℕ) (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin n)) (R r : ℝ) (hR : 0 < R)
    (hr : 0 < r) (hrR : r < R) (hsupp : tsupport f ⊆ Metric.ball x R) (i j : Fin n) :
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x)) =
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      fundamentalSolution n (x - y) * secondPartial f i j y)
    + f x * (R ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j ∂volume.toSphere))
    + r ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        fundamentalSolution n (-(r • w.1)) * partialDeriv f j (x + r • w.1) * w.1 i
        + partialDeriv (fundamentalSolution n) i (-(r • w.1)) *
          (f (x + r • w.1) - f x) * w.1 j ∂volume.toSphere) := by sorry
