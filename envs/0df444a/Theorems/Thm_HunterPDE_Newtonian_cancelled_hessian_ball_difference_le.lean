-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_cancelled_hessian_ball_difference_le
-- name    : HunterPDE.Newtonian.cancelled_hessian_ball_difference_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T16:27:49.484423+00:00
-- url     : https://prove2.me/theorems/a2f4bd69-d35b-4417-a9a2-96233ff525ae
-- title:
--   Uniform increment estimate for cancelled Newtonian Hessian integrals
-- statement:
--   Let $n\ge2$ and $0<\alpha<1$. There is a finite nonnegative constant $A$, depending only on $n$ and $\alpha$, with the following property. Suppose $f\in C_c^\infty(\mathbb R^n)$ and $H\ge0$ satisfies $|f(z)-f(w)|\le H\|z-w\|^\alpha$ for every $z,w$. For any points $x,x'$, radius $R>0$ with both $B_R(x)$ and $B_R(x')$ containing the closed support of $f$, and indices $i,j$, set
--
--   $$I_R f(z)=\int_{B_R(z)}\partial_{ij}\Gamma(z-y)(f(y)-f(z))\,dy.$$
--
--   Then $|I_R f(x)-I_R f(x')|\le A H\|x-x'\|^\alpha$. The constant is uniform in the source, indices, points and radius.
--
--   This isolates the singular-integral part of the Hölder estimate and makes no assertion about derivatives of the potential.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed pp. 39–43, Corollary 2.27 Eq. (2.29) and Theorem 2.28 proof, estimates (a), (b1), (b2), (c), Eqs. (2.32)–(2.34). Centered-ball formulation of the cancelled integral estimate.

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory HunterPDE.Newtonian
open scoped ContDiff NNReal

theorem HunterPDE.Newtonian.cancelled_hessian_ball_difference_le (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ H : ℝ≥0, (∀ x y, |f x - f y| ≤ (H : ℝ) * ‖x - y‖ ^ α) →
      ∀ x x' : EuclideanSpace ℝ (Fin n), ∀ R : ℝ, 0 < R →
        tsupport f ⊆ Metric.ball x R → tsupport f ⊆ Metric.ball x' R →
        ∀ i j : Fin n,
          |(∫ y in Metric.ball x R,
              secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x)) -
            (∫ y in Metric.ball x' R,
              secondPartial (fundamentalSolution n) i j (x' - y) * (f y - f x'))| ≤
            (A : ℝ) * (H : ℝ) * ‖x - x'‖ ^ α := by sorry
