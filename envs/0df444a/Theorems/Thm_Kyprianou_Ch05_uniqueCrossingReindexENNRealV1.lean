-- Prove2me | Theorems.Thm_Kyprianou_Ch05_uniqueCrossingReindexENNRealV1
-- name    : Kyprianou.Ch05.uniqueCrossingReindexENNRealV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:26:04.872803+00:00
-- url     : https://prove2.me/theorems/a34af5e8-40d1-47cb-b947-93fdc4a213e2
-- title:
--   Reindex a unique nonnegative crossing summand along injective active times
-- statement:
--   When a crossing time exists it corresponds to exactly one active index, and both sums equal its discount. If none exists both sums vanish.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.uniqueCrossingReindexENNRealV1
    {I T : Type} (clock : I → T) (C : I → Prop) (D : T → Prop)
    (g : T → ENNReal)
    (hmap : ∀ i, C i → D (clock i))
    (hinj : ∀ i j, C i → C j → clock i = clock j → i = j)
    (huniq : ∀ t u, D t → D u → t = u)
    (hsurj : ∀ t, D t → ∃ i, C i ∧ clock i = t) :
    (∑' i, if C i then g (clock i) else 0) =
      ∑' t, if D t then g t else 0 := by
  sorry
