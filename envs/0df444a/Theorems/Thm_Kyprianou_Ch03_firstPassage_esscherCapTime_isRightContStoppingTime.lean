-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassage_esscherCapTime_isRightContStoppingTime
-- name    : Kyprianou.Ch03.firstPassage_esscherCapTime_isRightContStoppingTime
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T01:40:56.922818+00:00
-- url     : https://prove2.me/theorems/95bd8d3c-56cb-4388-a1ed-5c81c1bbd3b1
-- title:
--   Capped first-passage time is an $F_+$-stopping time
-- statement:
--   Let $X$ be a spectrally negative Lévy process on a filtered probability space $(\Omega,\mathcal{F},(\mathcal{F}_t),P)$, and write $\tau_x^+ = \inf\{t>0:X_t>x\}$ for a barrier $x>0$. Let `finiteTime` be a selector for $\tau_x^+$ on $\{\tau_x^+<\infty\}$, and fix a deterministic horizon $T\ge 0$.
--
--   Define the capped first-passage time
--   $$\sigma := \tau_x^+ \wedge T$$
--   by using `finiteTime` on $\{\tau_x^+\le T\}$ and the constant $T$ otherwise. Then $\sigma$ is a stopping time for the right-continuous filtration $\mathcal{F}_+$ (i.e.\ `F.rightCont`), and $\sigma\le T$ pathwise.
--
--   This is the stopping-time input needed to apply the Esscher optional-sampling / mean-one identity at a bounded stopping time.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.12: τ_x^+ ∧ T is a bounded stopping time for the right-continuous filtration

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassage_esscherCapTime_isRightContStoppingTime
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : Real) (hx : 0 < x)
    (finiteTime : Omega → NNReal)
    (hfin : ∀ omega,
      firstHittingTime L.X (Set.Ioi x) omega != ⊤ →
        firstHittingTime L.X (Set.Ioi x) omega =
          (finiteTime omega : WithTop NNReal))
    (T : NNReal) :
    IsStoppingTime F.rightCont
      (fun omega =>
        ((if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
            finiteTime omega ≤ T
          then finiteTime omega
          else T) : WithTop NNReal)) ∧
    (∀ omega,
      (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
          finiteTime omega ≤ T
        then finiteTime omega
        else T) ≤ T) := by
  sorry

end Kyprianou.Ch03
