-- Prove2me | Theorems.Thm_Kyprianou_Ch06_cadlagFromPathRegularity
-- name    : Kyprianou.Ch06.cadlagFromPathRegularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:02:42.278141+00:00
-- url     : https://prove2.me/theorems/e297a96c-1eec-4070-a310-ae1efef042aa
-- title:
--   Chapter 6 bridge: right continuity and left limits imply IsCadlag
-- statement:
--   If almost every path is right-continuous at every nonnegative time and admits a left limit at every strictly positive time, almost every path satisfies the published ProbabilityTheory.IsCadlag predicate. At the minimal time zero, the left-hand neighbourhood is empty and the left-limit condition holds vacuously.
-- source:
--   Kyprianou (2006), Chapter 6 Lévy-process sample-path assumptions; source-faithful compatibility lemma with the published LeanLevy càdlàg predicate.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag

set_option autoImplicit false
open MeasureTheory Filter
open scoped NNReal

theorem Kyprianou.Ch06.cadlagFromPathRegularity
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hregular : ∀ᵐ ω ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u : NNReal => X u ω) (Set.Ici t) t ∧
      (t = 0 ∨ ∃ x : Real,
        Tendsto (fun u : NNReal => X u ω)
          (nhdsWithin t (Set.Iio t)) (nhds x))) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag (fun t : NNReal => X t ω) := by sorry
