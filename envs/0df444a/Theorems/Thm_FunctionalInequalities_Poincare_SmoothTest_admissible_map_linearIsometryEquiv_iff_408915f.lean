-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_admissible_map_linearIsometryEquiv_iff_408915f
-- name    : FunctionalInequalities.Poincare.SmoothTest.admissible_map_linearIsometryEquiv_iff_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:38:37.294182+00:00
-- url     : https://prove2.me/theorems/4ff0804f-e221-4f50-9526-ae241fd32e10
-- title:
--   Admissibility Under a Linear Isometry Equivalence
-- statement:
--   This is the exact test-domain correspondence for a linear isometry equivalence.
--
--   Let $E$ and $F$ be complete real inner-product normed spaces equipped with measurable Borel structures. Let $e:E\simeq F$ be a linear isometry equivalence, let $\mu$ be a probability measure on $E$, and let $f:F\to\mathbb R$. Then
--
--   $$
--   \operatorname{Admissible}(e_*\mu,f)
--   \iff
--   \operatorname{Admissible}(\mu,f\circ e),
--   $$
--
--   where $e_*\mu=\operatorname{Measure.map}(e,\mu)$.
--
--   This result allows the smooth admissible test class to be transferred in either direction across an isometric change of variables.
--
--   **Formalization Note**: `Admissible` is the repository's fixed smooth test-domain predicate. The measure transport is `μ.map e`, and the equivalence is used together with its inverse.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/Transport.lean#L149-L167 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.Transport`, declaration `FunctionalInequalities.Poincare.SmoothTest.admissible_map_linearIsometryEquiv_iff`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
section IsometryTransport
variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
variable (e : E ≃ₗᵢ[ℝ] F) (μ : Measure E) [IsProbabilityMeasure μ]

theorem FunctionalInequalities.Poincare.SmoothTest.admissible_map_linearIsometryEquiv_iff_408915f {f : F → ℝ} :
    Admissible (μ.map e) f ↔ Admissible μ (f ∘ e) := by sorry
