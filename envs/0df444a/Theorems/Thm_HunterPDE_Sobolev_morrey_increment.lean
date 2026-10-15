-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_morrey_increment
-- name    : HunterPDE.Sobolev.morrey_increment
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T21:36:32.085673+00:00
-- url     : https://prove2.me/theorems/4b0892e2-4598-4a5b-8e37-d92a4f74e8d8
-- title:
--   Morrey pointwise increment estimate for compactly supported C1 functions
-- statement:
--   Let $n\ge0$, $n<p<\infty$, and $\alpha=1-n/p$. There exists $A=A(n,p)\ge0$, chosen before the function, such that every compactly supported continuously differentiable $f:\mathbb R^n\to\mathbb R$ satisfies
--   $$|f(x)-f(y)|\le A\|Df\|_{L^p(\mathbb R^n)}|x-y|^{\alpha}\qquad(x,y\in\mathbb R^n).$$
--   Here $|Df|$ is the Euclidean gradient length. This estimate controls the modulus of continuity independently of the support size and is the pointwise analytic step underlying Morrey embedding.
--
--   **Formalization Note.** The statement uses extended nonnegative real norms and includes equal points and dimension zero. The C1 hypothesis is the differentiability actually used by the source's segment integration argument.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, pp. 68–70, proof of Theorem 3.36, equation (3.16); C1 formulation of the same argument

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

theorem HunterPDE.Sobolev.morrey_increment {n : ℕ} {p : ℝ} (hnp : (n : ℝ) < p) :
    ∃ A : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ x y, ENNReal.ofReal |f x - f y| ≤
        (A : ENNReal) * eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p) volume *
          ENNReal.ofReal (‖x - y‖ ^ (1 - (n : ℝ) / p)) := by sorry
