-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_cancelled_hessian_inner_error_bound
-- name    : HunterPDE.Newtonian.cancelled_hessian_inner_error_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T10:33:26.794675+00:00
-- url     : https://prove2.me/theorems/eaf8b5e6-0278-4bd1-b152-a6a64a46bcc9
-- title:
--   Quantitative C1 estimate for the Newtonian inner boundary error
-- statement:
--   Let $n\ge2$ and $f\in C^1(\mathbb R^n)$. Fix a point $x$ and coordinate indices $i,j$, and let $\Gamma$ be the Newtonian fundamental solution. Put
--
--   $$E_{ij}(r)=r^{n-1}\int_{S^{n-1}}\left[\Gamma(-r\omega)\partial_jf(x+r\omega)\omega_i+\partial_i\Gamma(-r\omega)(f(x+r\omega)-f(x))\omega_j\right]dS(\omega).$$
--
--   There is a constant $C\ge0$, depending on $n,f,x,i,j$, such that for every $0<r\le1$,
--
--   $$|E_{ij}(r)|\le C\left(r+r^{n-1}|\Gamma(r e_i)|\right).$$
--
--   Here $e_i$ is the unit coordinate vector. No compact support assumption is needed. The bound quantifies the error from the inner boundary in Newtonian integration by parts; its right side is of order $r$ for $n\ge3$ and at most order $r+r|\log r|$ for $n=2$.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed pp. 37–38, Eqs. (2.27)–(2.28) and subsequent inner-boundary estimates; finite-radius identity and quantitative C1 formulation.

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
open MeasureTheory HunterPDE.Newtonian Filter
open scoped ContDiff Topology

theorem HunterPDE.Newtonian.cancelled_hessian_inner_error_bound
    (n : ℕ) (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
    ‖r ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        fundamentalSolution n (-(r • w.1)) * partialDeriv f j (x + r • w.1) * w.1 i
        + partialDeriv (fundamentalSolution n) i (-(r • w.1)) *
          (f (x + r • w.1) - f x) * w.1 j ∂volume.toSphere)‖ ≤
      C * (r + ‖fundamentalSolution n (r • EuclideanSpace.single i 1) * r ^ (n - 1)‖) := by sorry
