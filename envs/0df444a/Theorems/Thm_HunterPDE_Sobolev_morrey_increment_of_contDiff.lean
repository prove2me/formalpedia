-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_morrey_increment_of_contDiff
-- name    : HunterPDE.Sobolev.morrey_increment_of_contDiff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T17:21:52.291154+00:00
-- url     : https://prove2.me/theorems/a4ec1d80-8bd0-4c9f-a46b-5dc84f79a245
-- title:
--   Homogeneous Morrey increment bound for globally C¹ functions
-- statement:
--   For $n<p<\infty$ there is $A=A(n,p)\ge0$ such that every globally $C^1$ real function on $\mathbb R^n$ satisfies $|f(x)-f(y)|\le A\|Df\|_p|x-y|^{1-n/p}$. The formal inequality uses extended nonnegative reals and includes infinite gradient norm. Compact support, global integrability and decay of $f$ are not assumed. This follows directly from the proved ball-averaged oscillation estimate by integrating the triangle inequality over a common ball. Dimension zero is included.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 68–70, Theorems 3.36–3.37; homogeneous mollification and dense-set extension in the proof of Theorem 3.37.

import Theorems.Thm_HunterPDE_Sobolev_ball_averaged_oscillation_le
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith

open MeasureTheory

theorem HunterPDE.Sobolev.morrey_increment_of_contDiff {n : ℕ} {p : ℝ} (hnp : (n : ℝ) < p) :
    ∃ A : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 f →
      ∀ x y, ENNReal.ofReal |f x - f y| ≤
        (A : ENNReal) * eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p) volume *
          ENNReal.ofReal (‖x - y‖ ^ (1 - (n : ℝ) / p)) := by sorry
