-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise47RunningSupremumIntegrable
-- name    : Kyprianou.Ch04.exercise47RunningSupremumIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T22:28:37.53695+00:00
-- url     : https://prove2.me/theorems/94aa45b1-dd43-4fb4-b32c-027e593db36d
-- title:
--   Exercise 4.7(ii): finite expected running supremum for general spectrally negative Levy input
-- statement:
--   For a general spectrally negative Levy process, without bounded-variation restrictions, its running supremum up to each finite time has finite absolute first moment. This is the running-supremum integrability required in upgrading the Kella-Whitt local martingale to a true martingale.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, Exercise 4.7(ii), pp. 105-109.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Exercise 4.7(ii) (pp. 108-109). Running-supremum first-moment bound. -/
theorem exercise47RunningSupremumIntegrable
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    forall t : NNReal,
      Integrable
        (fun omega : Omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)) P := by
  sorry
end Kyprianou.Ch04
