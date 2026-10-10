-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_tendsto_cancelled_hessian_punctured_ball
-- name    : HunterPDE.Newtonian.tendsto_cancelled_hessian_punctured_ball
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-10T10:11:45.111142+00:00
-- url     : https://prove2.me/theorems/bfb99e3e-757b-4dcf-88e0-2b0545230135
-- title:
--   Punctured integration by parts for the cancelled Newtonian Hessian
-- statement:
--   Let n≥2 and let f be twice continuously differentiable with compact support contained in the open ball B_R(x), where R>0. Put r_k=1/(k+1) and Γ equal to the Newtonian fundamental solution. Then
--
--   $$\lim_{k\to\infty}\int_{B_R(x)\setminus\overline B_{r_k}(x)}\partial_{ij}\Gamma(x-y)(f(y)-f(x))\,dy=\int_{\mathbb R^n}\Gamma(x-y)\partial_{ij}f(y)\,dy+f(x)R^{n-1}\int_{S^{n-1}}\partial_i\Gamma(-R\omega)\omega_j\,dS(\omega).$$
--
--   This is the punctured-domain integration-by-parts step of Hunter Eqs. (2.26)–(2.28), specialized to a ball and a positive sequence tending to zero. The C2 assumption suffices for two integrations by parts and boundedness of the first and second derivatives on compact sets. The two inner boundary errors vanish: the gradient term contains f(y)-f(x), and the fundamental-solution term is O(r) for n≥3 and O(r|log r|) for n=2. The statement does not identify the limit with the full cancelled integral; absolute integrability and dominated convergence perform that separate step.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed pp. 37–38, Theorem 2.26, Eqs. (2.26)–(2.28).

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
open MeasureTheory HunterPDE.Newtonian Filter
open scoped ContDiff Topology

theorem HunterPDE.Newtonian.tendsto_cancelled_hessian_punctured_ball
    (n : ℕ) (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R)
    (hsupp : tsupport f ⊆ Metric.ball x R) (i j : Fin n) :
    Tendsto (fun k : ℕ =>
      ∫ y in Metric.ball x R \ Metric.closedBall x (1 / ((k : ℝ) + 1)),
        secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x))
      atTop (𝓝 ((∫ y, fundamentalSolution n (x - y) * secondPartial f i j y)
        + f x * (R ^ (n - 1) *
          (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
            partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j ∂volume.toSphere)))) := by sorry
