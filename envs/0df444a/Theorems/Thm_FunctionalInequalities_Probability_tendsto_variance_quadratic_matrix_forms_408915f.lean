-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_tendsto_variance_quadratic_matrix_forms_408915f
-- name    : FunctionalInequalities.Probability.tendsto_variance_quadratic_matrix_forms_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:26:22.459659+00:00
-- url     : https://prove2.me/theorems/c8b2bde3-0d28-4f3c-a3d9-09f97fc7bf91
-- title:
--   Continuity of Variance for Quadratic Matrix Forms
-- statement:
--   This formalizes the coefficient-continuity part of Lemma A.2 of Letwin (arXiv:2607.24164v1), cited as “Reduction to invertible $M$.”
--
--   Let $\mu$ be a probability measure on $E=\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$ with finite fourth moment. Let $A_k$ and $A$ be real $n\times n$ matrices with $A_k\to A$ entrywise (equivalently in the finite-dimensional matrix topology). Then
--
--   $$\operatorname{Var}_{\mu}\!\left(x\mapsto\sum_{i,j}(A_k)_{ij}x_i x_j\right)
--   \longrightarrow
--   \operatorname{Var}_{\mu}\!\left(x\mapsto\sum_{i,j}A_{ij}x_i x_j\right).$$
--
--   The declaration supplies the fourth-moment continuity needed in singular extensions of matrix variance bounds; it does not itself assert a numerical variance estimate.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.2. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/QuadraticVariance.lean#L23-L53 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.QuadraticVariance`, declaration `FunctionalInequalities.Probability.tendsto_variance_quadratic_matrix_forms`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
set_option maxHeartbeats 500000

theorem FunctionalInequalities.Probability.tendsto_variance_quadratic_matrix_forms_408915f {n : ℕ}
    (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (h4 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 4 (mu : Measure _))
    {seq : ℕ → Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hseq : Tendsto seq atTop (𝓝 A)) :
    Tendsto (fun k => ProbabilityTheory.variance
      (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, seq k i j * x i * x j) (mu : Measure _))
      atTop (𝓝 (ProbabilityTheory.variance
        (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, A i j * x i * x j) (mu : Measure _))) := by sorry
