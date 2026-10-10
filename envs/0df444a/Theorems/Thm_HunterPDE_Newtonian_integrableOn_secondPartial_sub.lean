-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_integrableOn_secondPartial_sub
-- name    : HunterPDE.Newtonian.integrableOn_secondPartial_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T22:58:44.950238+00:00
-- url     : https://prove2.me/theorems/8fd26a4a-fabb-4062-8dce-c88fa99e80e0
-- title:
--   Cancellation makes the Newtonian Hessian integrable against C1 data
-- statement:
--   Let $n\ge2$ and let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable. For every $x$, every finite radius $R>0$, and every pair of coordinate indices $i,j$, the cancelled Newtonian Hessian is absolutely integrable:
--
--   $$\int_{B_R(x)}|\partial_{ij}\Gamma(x-y)(f(y)-f(x))|\,dy<\infty.$$
--
--   No compact support assumption is needed. On a fixed ball, the C1 bound gives $|f(y)-f(x)|\le C|y-x|$, while the Hessian is bounded by a constant times $|y-x|^{-n}$. The product has the locally integrable majorant $C|y-x|^{1-n}$. This is the integrability step of Hunter Theorem 2.26, p. 38, generalized from smooth compactly supported data to C1 data.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, pp. 37–39, Theorem 2.26 Eqs. (2.25)–(2.28), Corollary 2.27 Eq. (2.29).

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory HunterPDE.Newtonian
open scoped ContDiff

theorem HunterPDE.Newtonian.integrableOn_secondPartial_sub (n : ℕ) (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R) (i j : Fin n) :
    IntegrableOn (fun y => secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x))
      (Metric.ball x R) := by sorry
