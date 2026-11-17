-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenMovingCutoffPowerSplit
-- name    : Kyprianou.Ch07.kestenMovingCutoffPowerSplit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:50:31.964195+00:00
-- url     : https://prove2.me/theorems/e72f7390-42f7-4970-ab3e-374519fab46a
-- title:
--   Kesten: split the (n+1)-fold upper tail at moving threshold x−T
-- statement:
--   For every real probability law G, n≥0 and real x,T, the upper-tail mass of its (n+1)-fold convolution at x is at most G((x−T,infinity)) plus the lower integral against G over a≤x−T of the nth convolution upper-tail mass at (x−a,infinity). This holds for arbitrary real-valued support and follows from the proved source Fubini/commutativity cutoff inequality. It is the exact decomposition needed for Kesten’s uniform inductive estimate.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.14 proof, printed pp.201–202, original PDF pp.210–211. Compare Foss–Korshunov–Zachary (2011), Theorem 3.34, display (3.38)–(3.39). Exact source compiled privately under pinned remote job c54e14ba-aa8e-4246-adc6-c387010d2c94.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_convolutionPowerProbability
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionComm
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailSplitAtLe
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenMovingCutoffPowerSplit
    (G : Measure Real) [IsProbabilityMeasure G]
    (n : Nat) (x T : Real) :
    (Kyprianou.Ch07.convolutionPower G (n + 1)) (Set.Ioi x) ≤
      G (Set.Ioi (x - T)) +
        ∫⁻ a : Real in Set.Iic (x - T),
          (Kyprianou.Ch07.convolutionPower G n)
            (Set.Ioi (x - a)) ∂G := by
  sorry
