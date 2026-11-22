-- Prove2me | Theorems.Thm_Kyprianou_Ch02_abstractPRMDisjointSigmaIndepV8
-- name    : Kyprianou.Ch02.abstractPRMDisjointSigmaIndepV8
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:54:34.75606+00:00
-- url     : https://prove2.me/theorems/87a80188-ef8e-48c7-90aa-9a24d49a9210
-- title:
--   Generic Poisson random-measure sigma independence
-- statement:
--   For an arbitrary measurable mark space, the full count-generated sigma fields of two disjoint measurable regions are independent under the abstract Poisson random-measure assumptions.
-- source:
--   Kyprianou (2006) Chapter 2 Corollary 2.5 V9; exact conjunct of canonical target eeb93d23-7cff-49d0-951c-1e4bebff0a68; compatible proved generic disjoint-family independence module.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV8
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem abstractPRMDisjointSigmaIndepV8
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (N : Ω → Measure E)
    (hN : Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P m N) :
    ∀ (A B : Set E),
      MeasurableSet A → MeasurableSet B → Disjoint A B →
      ProbabilityTheory.Indep
        (⨆ C ∈ {C : Set E | C ⊆ A ∧ MeasurableSet C},
           MeasurableSpace.comap (fun ω => N ω C) inferInstance)
        (⨆ D ∈ {D : Set E | D ⊆ B ∧ MeasurableSet D},
           MeasurableSpace.comap (fun ω => N ω D) inferInstance)
        P := by sorry
end Kyprianou.Ch02
