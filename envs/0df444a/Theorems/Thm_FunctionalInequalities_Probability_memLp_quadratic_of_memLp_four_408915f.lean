-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_memLp_quadratic_of_memLp_four_408915f
-- name    : FunctionalInequalities.Probability.memLp_quadratic_of_memLp_four_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:26:17.987038+00:00
-- url     : https://prove2.me/theorems/477b3f67-5f32-49d8-9986-cdad81abf577
-- title:
--   Quadratic Forms Preserve $L^4$ Integrability at Exponent $2$
-- statement:
--   This is a general moment-transfer lemma for quadratic forms.
--
--   Let $(\alpha,\mu)$ be a measurable space with a measure, let $E$ be a real inner-product normed group, let $f:\alpha\to E$ satisfy `MemLp f 4 μ`, and let $A:E\to E$ be a continuous linear map. Then the scalar quadratic form $x\mapsto\langle A(f(x)),f(x)\rangle$ belongs to `MemLp` with exponent $2$:
--
--   $$x\longmapsto\langle A(f(x)),f(x)\rangle\in L^2(\mu).$$
--
--   The lemma is a reusable integrability fact for quadratic observables, with no probability, finite-dimensionality, or measurability assumption on $f$ beyond the stated `MemLp` hypothesis.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Moments.lean#L509-L531 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Moments`, declaration `FunctionalInequalities.Probability.memLp_quadratic_of_memLp_four`; the repository is private at upload time).

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

open MeasureTheory
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
set_option maxHeartbeats 300000

theorem FunctionalInequalities.Probability.memLp_quadratic_of_memLp_four_408915f {alpha E : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {mu : Measure alpha}
    {f : alpha → E} (hf : MemLp f 4 mu) (A : E →L[ℝ] E) :
    MemLp (fun x => ⟪A (f x), f x⟫) 2 mu := by sorry
