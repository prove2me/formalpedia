-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_centered_ball_oscillation_le_potential
-- name    : HunterPDE.Sobolev.centered_ball_oscillation_le_potential
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T06:58:41.473343+00:00
-- url     : https://prove2.me/theorems/6890fdb8-3da3-4f2f-a862-6506adb53931
-- title:
--   Centered C1 oscillation controlled by the gradient potential
-- statement:
--   Let $n\ge1$. There is a finite constant $C_n\ge0$ such that every $C^1$ function $f:\mathbb R^n\to\mathbb R$, center $x$, and radius $r>0$ satisfy
--
--   $$\int_{B(x,r)}|f(x)-f(z)|\,dz\le |B(x,r)|C_n\int_{B(x,r)}|\nabla f(z)|\,|z-x|^{1-n}\,dz.$$
--
--   This centered estimate expresses mean oscillation in terms of a first-order potential and can be used independently of any choice of Lebesgue exponent. Compact support is not required.
--
--   **Formalization Note** Both integrals are nonnegative extended integrals. Real powers specify the value of the kernel at the center; that value does not affect a Lebesgue integral.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, pp. 68–69, proof of Theorem 3.36, equation (3.14). The argument uses only C1 regularity and is stated here without the unused compact-support hypothesis.

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory
set_option autoImplicit false

theorem HunterPDE.Sobolev.centered_ball_oscillation_le_potential {n : ℕ} (hn : 0 < n) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 f → ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ z in Metric.ball x r, ENNReal.ofReal |f x - f z|) ≤
        volume (Metric.ball x r) * (C : ENNReal) *
          (∫⁻ z in Metric.ball x r, ENNReal.ofReal ‖gradient f z‖ *
            ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) := by sorry
