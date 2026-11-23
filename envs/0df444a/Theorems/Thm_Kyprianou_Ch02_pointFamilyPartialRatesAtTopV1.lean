-- Prove2me | Theorems.Thm_Kyprianou_Ch02_pointFamilyPartialRatesAtTopV1
-- name    : Kyprianou.Ch02.pointFamilyPartialRatesAtTopV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:06:54.73315+00:00
-- url     : https://prove2.me/theorems/0f5e2f91-fc78-4991-a76d-63521d0ea952
-- title:
--   pointFamilyPartialRatesAtTopV1
-- statement:
--   Linear rate exhaustion: sigma-finite Poisson partition piece rates sum to the full intensity; when m(A)=∞ the nonnegative partial sums of their toNNReal rates tend to infinity.
-- source:
--   Kyprianou (2006), Chapter 2, original PRM existence. Exact LeanLevy.RandomMeasure.PoissonRandomMeasure and PoissonPointFamily source reduction.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem pointFamilyPartialRatesAtTopV1
    {E : Type} [MeasurableSpace E] (m : Measure E)
    [SigmaFinite m] [Nonempty E]
    (A : Set E) (hA : MeasurableSet A) (hInf : m A = ⊤) :
    Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
        (m (ProbabilityTheory.prmPiece m k ∩ A)).toNNReal)
      atTop atTop := by sorry
end Kyprianou.Ch02
