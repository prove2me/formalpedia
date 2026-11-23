-- Prove2me | Theorems.Thm_Kyprianou_Ch02_integerValuedFiniteDiracV1
-- name    : Kyprianou.Ch02.integerValuedFiniteDiracV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:17:41.980797+00:00
-- url     : https://prove2.me/theorems/db4a61fd-eb50-41b9-ac96-d32d091678bd
-- title:
--   Finite integer-valued measures are finite Dirac sums
-- statement:
--   A finite integer-valued measure on a countably separated space is a finite sum of Dirac masses at its finitely many support points. Derive this from the Proved Chapter 2 integerValuedFiniteSupportV1 theorem and the source KLS measure equality lemma Measure.ae_mem_finset_iff. It directly supports the finite-window Poisson Dirac law.
-- source:
--   LevyStochCalc/Probability/IntegerValuedMeasure.lean, atomicity; Kyprianou Chapter 2 Lemma 2.8.

import Mathlib
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F003
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem integerValuedFiniteDiracV1
    {α : Type} [MeasurableSpace α]
    [MeasurableSpace.CountablySeparated α]
    (μ : Measure α)
    (hint : LevyStochCalc.Probability.IsIntegerValued μ) :
    ∃ s : Finset α, μ = ∑ a ∈ s, μ {a} • Measure.dirac a := by sorry
end Kyprianou.Ch02
