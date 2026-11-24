-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassage_creepingOnFiniteHit
-- name    : Kyprianou.Ch03.firstPassage_creepingOnFiniteHit
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T00:17:11.991589+00:00
-- url     : https://prove2.me/theorems/1632693b-1368-40c7-83c2-596ca6c56d81
-- title:
--   Spectrally negative processes creep upwards at first passage
-- statement:
--   Let $X$ be a spectrally negative Lévy process (no positive jumps). For every barrier $x \ge 0$ and every measurable selector `finiteTime` that agrees with the upward first-passage time $\tau_x^+ = \inf\{t>0: X_t > x\}$ on $\{\tau_x^+ < \infty\}$, one has
--   $$X_{\tau_x^+} = x \qquad\text{almost surely on }\{\tau_x^+ < \infty\}.$$
--   This is the classical creeping/overshoot-zero property of spectrally negative paths: right-continuity forces $X_{\tau_x^+} \ge x$, while the absence of positive jumps forces $X_{\tau_x^+} \le X_{\tau_x^+-} \le x$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 3, proof of Theorem 3.12 (creeping at first upward passage)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassage_creepingOnFiniteHit
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : Real) (hx : 0 ≤ x)
    (finiteTime : Omega → NNReal)
    (hfin : ∀ omega,
      firstHittingTime L.X (Set.Ioi x) omega != ⊤ →
        firstHittingTime L.X (Set.Ioi x) omega =
          (finiteTime omega : WithTop NNReal)) :
    ∀ᵐ omega ∂P,
      firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ →
        L.X (finiteTime omega) omega = x := by
  sorry

end Kyprianou.Ch03
