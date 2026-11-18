-- Prove2me | Theorems.Thm_Kyprianou_poissonRestrictionAndIndependenceGenericCh02V9
-- name    : Kyprianou.poissonRestrictionAndIndependenceGenericCh02V9
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T12:48:01.469876+00:00
-- url     : https://prove2.me/theorems/eeb93d23-7cff-49d0-951c-1e4bebff0a68
-- title:
--   Corollary 2.5 V9: source-general restriction and independence
-- statement:
--   On an arbitrary sigma-finite measurable space, prove the restriction and disjoint generated-count sigma-algebra independence consequences for an actual abstract Poisson random measure with almost surely integer-valued-or-infinite counts on every measurable set simultaneously.
-- source:
--   Kyprianou (2006), Corollary 2.5, printed p. 40 (full original PDF physical p. 51)

import Mathlib
import Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV8
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem poissonRestrictionAndIndependenceGenericCh02V9
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (N : Ω → Measure E)
    (hN : Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P m N) :
    (∀ (B : Set E), MeasurableSet B →
      Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P
        (m.restrict B) (fun ω => (N ω).restrict B)) ∧
    (∀ (A B : Set E),
      MeasurableSet A → MeasurableSet B → Disjoint A B →
      ProbabilityTheory.Indep
        (⨆ C ∈ {C : Set E | C ⊆ A ∧ MeasurableSet C},
           MeasurableSpace.comap (fun ω => N ω C) inferInstance)
        (⨆ D ∈ {D : Set E | D ⊆ B ∧ MeasurableSet D},
           MeasurableSpace.comap (fun ω => N ω D) inferInstance)
        P) := by sorry

end Kyprianou
