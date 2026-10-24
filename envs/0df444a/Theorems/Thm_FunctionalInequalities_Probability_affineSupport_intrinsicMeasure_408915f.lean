-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_affineSupport_intrinsicMeasure_408915f
-- name    : FunctionalInequalities.Probability.affineSupport_intrinsicMeasure_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:13.2561+00:00
-- url     : https://prove2.me/theorems/78b88677-236e-49c2-a1bc-06f21b8df6d5
-- title:
--   Full Affine Support of the Intrinsic Measure
-- statement:
--   This establishes the geometric fullness of intrinsic coordinates.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure and second-countable topology, and let $\mu$ be any probability measure on $E$. Let $V$ be the direction space of the affine support of $\mu$, and let `intrinsicMeasure μ` be the corresponding intrinsic probability measure on $V$. Then
--
--   $$
--   \operatorname{affineSupport}(\operatorname{intrinsicMeasure}(\mu))=V.
--   $$
--
--   The statement is purely geometric: the intrinsic construction removes redundant affine directions and leaves a law with full affine support.
--
--   **Formalization Note** No second-moment, log-concavity, density, or absolute-continuity hypothesis is assumed; completeness is omitted from the declaration's required assumptions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/AffineSupport.lean#L215-L233 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.AffineSupport`, declaration `FunctionalInequalities.Probability.affineSupport_intrinsicMeasure`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support

noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
section Coordinates
variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
omit [CompleteSpace E]

theorem FunctionalInequalities.Probability.affineSupport_intrinsicMeasure_408915f (μ : ProbabilityMeasure E) :
    affineSupport (intrinsicMeasure μ) = ⊤ := by sorry
