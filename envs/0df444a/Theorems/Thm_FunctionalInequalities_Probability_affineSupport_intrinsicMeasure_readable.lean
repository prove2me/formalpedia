-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_affineSupport_intrinsicMeasure_readable
-- name    : FunctionalInequalities.Probability.affineSupport_intrinsicMeasure_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:23.857212+00:00
-- url     : https://prove2.me/theorems/69034b90-b400-423d-8cf5-e41038da0be1
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem affineSupport_intrinsicMeasure (μ : ProbabilityMeasure E) :
--       affineSupport (intrinsicMeasure μ) = ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81).
--
--   [Source excerpt, lines 218–219](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/AffineSupport.lean#L218-L219) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/AffineSupport.lean#L215-L233 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.AffineSupport`, declaration `FunctionalInequalities.Probability.affineSupport_intrinsicMeasure`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport

open MeasureTheory
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
variable [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
omit [CompleteSpace E]

theorem FunctionalInequalities.Probability.affineSupport_intrinsicMeasure_readable (μ : ProbabilityMeasure E) :
    affineSupport (intrinsicMeasure μ) = ⊤ := by sorry
