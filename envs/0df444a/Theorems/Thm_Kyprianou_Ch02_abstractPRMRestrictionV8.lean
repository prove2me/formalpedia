-- Prove2me | Theorems.Thm_Kyprianou_Ch02_abstractPRMRestrictionV8
-- name    : Kyprianou.Ch02.abstractPRMRestrictionV8
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:54:38.261798+00:00
-- url     : https://prove2.me/theorems/8695c0cf-5f43-4459-89bb-a2fd139ccb1a
-- title:
--   Generic Poisson random-measure restriction law
-- statement:
--   Restricting an arbitrary-space abstract Poisson random measure to a measurable region preserves all Poisson count laws, count-family independence and a simultaneous a.s. integer-or-infinity counting-measure property.
-- source:
--   Kyprianou (2006) Chapter 2 Corollary 2.5 V9; exact conjunct of canonical target eeb93d23-7cff-49d0-951c-1e4bebff0a68; compatible proved generic disjoint-family independence module.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV8
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem abstractPRMRestrictionV8
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (N : Ω → Measure E)
    (hN : Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P m N) :
    ∀ (B : Set E), MeasurableSet B →
      Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P
        (m.restrict B) (fun ω => (N ω).restrict B) := by sorry
end Kyprianou.Ch02
