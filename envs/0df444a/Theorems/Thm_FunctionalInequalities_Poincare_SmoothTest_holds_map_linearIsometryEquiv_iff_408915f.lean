-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_map_linearIsometryEquiv_iff_408915f
-- name    : FunctionalInequalities.Poincare.SmoothTest.holds_map_linearIsometryEquiv_iff_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:38:38.002878+00:00
-- url     : https://prove2.me/theorems/d2c81c64-693d-4d61-ac79-ba204331b006
-- title:
--   Poincaré Inequality Invariance Under Isometries
-- statement:
--   This is the transport equivalence for the fixed-constant smooth-test Poincaré statement.
--
--   Let $E$ and $F$ be complete real inner-product normed spaces equipped with measurable Borel structures. Let $e:E\simeq F$ be a linear isometry equivalence, let $\mu$ be a probability measure on $E$, and let $C\in\mathbb R$. Then
--
--   $$
--   \operatorname{Holds}(e_*\mu,C)
--   \iff
--   \operatorname{Holds}(\mu,C),
--   $$
--
--   where $e_*\mu=\operatorname{Measure.map}(e,\mu)$.
--
--   The declaration records that the repository's smooth-test Poincaré inequality with constant $C$ is unchanged by a linear isometric equivalence of the underlying space.
--
--   **Formalization Note**: `Holds` is the fixed-constant predicate used by the smooth-test Poincaré development. The statement is an iff and does not identify `Holds` with a closed Dirichlet-form domain.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/Transport.lean#L187-L209 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.Transport`, declaration `FunctionalInequalities.Poincare.SmoothTest.holds_map_linearIsometryEquiv_iff`; the repository is private at upload time).

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

theorem FunctionalInequalities.Poincare.SmoothTest.holds_map_linearIsometryEquiv_iff_408915f {C : ℝ} :
    Holds (μ.map e) C ↔ Holds μ C := by sorry
