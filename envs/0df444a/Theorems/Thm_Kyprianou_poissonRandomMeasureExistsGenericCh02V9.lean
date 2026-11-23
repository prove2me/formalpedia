-- Prove2me | Theorems.Thm_Kyprianou_poissonRandomMeasureExistsGenericCh02V9
-- name    : Kyprianou.poissonRandomMeasureExistsGenericCh02V9
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:46:43.160964+00:00
-- url     : https://prove2.me/theorems/91c951f0-bb58-41af-a340-c7a168ec9ce3
-- title:
--   Theorem 2.4 V9: existence of an arbitrary-space Poisson counting measure
-- statement:
--   For every sigma-finite measurable intensity space, construct a probability space and actual Poisson random measure satisfying Definition 2.3, including count values in natural numbers or infinity simultaneously on all measurable sets outside a single null event.
-- source:
--   Kyprianou (2006), Theorem 2.4, printed pp. 38–40 (full original PDF physical pp. 49–51)

import Mathlib
import Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV8
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem poissonRandomMeasureExistsGenericCh02V9
    (E : Type) [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m] :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ N : Ω → Measure E,
          Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P m N
    := by sorry

end Kyprianou
