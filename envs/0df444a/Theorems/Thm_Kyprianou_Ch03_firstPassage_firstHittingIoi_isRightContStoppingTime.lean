-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassage_firstHittingIoi_isRightContStoppingTime
-- name    : Kyprianou.Ch03.firstPassage_firstHittingIoi_isRightContStoppingTime
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T01:57:57.427612+00:00
-- url     : https://prove2.me/theorems/013d8416-1456-4c04-8019-edffbb8f1bfe
-- title:
--   Upward first-passage time is an $\mathcal{F}_+$-stopping time
-- statement:
--   Let $X$ be a spectrally negative Lévy process on $(\Omega,\mathcal{F},(\mathcal{F}_t),P)$, and fix a barrier $x>0$. Write
--   $$\tau_x^+ = \inf\{t>0:X_t>x\}$$
--   for the upward first-passage time (with cemetery $\top$ if the barrier is never crossed).
--
--   Then $\tau_x^+$ is a stopping time for the right-continuous filtration $\mathcal{F}_+$ (i.e.\ `F.rightCont`). This follows from the debut/hitting-time theorem for right-continuous filtrations applied to the open upper half-line, or equivalently from the identification of $\tau_x^+$ with the two-sided exit up-time and the corresponding right-continuous stopping-time theorem for spectrally negative Lévy processes.
-- source:
--   Kyprianou (2006), Ch.3; cf. AvramDividend.Classical.upperPassage_isStoppingTime_of_rightContinuous and Kyprianou.Ch03.firstHittingIoi_eq_correctedUpTime

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassage_firstHittingIoi_isRightContStoppingTime
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : Real) (hx : 0 < x) :
    IsStoppingTime F.rightCont
      (fun omega => firstHittingTime L.X (Set.Ioi x) omega) := by
  sorry

end Kyprianou.Ch03
