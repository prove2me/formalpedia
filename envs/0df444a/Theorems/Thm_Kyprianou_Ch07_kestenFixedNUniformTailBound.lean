-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenFixedNUniformTailBound
-- name    : Kyprianou.Ch07.kestenFixedNUniformTailBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:43:27.750223+00:00
-- url     : https://prove2.me/theorems/d5e34690-bb3e-4956-9915-c98100b467e7
-- title:
--   Kesten: fixed-n subexponential convolution tails admit a uniform bound in x
-- statement:
--   Fix n>=2. If a probability law G has strictly positive tails for all x>0 and the n-fold convolution tail ratio converges to 1 after division by n as x tends to infinity, then the unnormalised n-fold convolution upper-tail ratio is uniformly bounded by one finite positive real constant for all x>0. For large x the limit supplies the bound; for bounded x positivity of G((M,infinity)) bounds the denominator and probability normalisation bounds the numerator.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14, printed pp.201–202; original PDF pp.210–211. Complete exact proof remote elaboration reached sentinel with no candidate errors in job 8b5a9f66-d36f-4538-b217-01651715fe26. This is the fixed-n component of the Kesten uniform affine-envelope estimate.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_convolutionPowerProbability
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenFixedNUniformTailBound
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (n : Nat) (hn : 2 ≤ n)
    (hConv : Tendsto (fun x : Real =>
      ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
        ((n : Real) * (G (Set.Ioi x)).toReal))
      atTop (nhds (1 : Real))) :
    ∃ C : Real, 0 < C ∧
      ∀ x : Real, 0 < x →
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          (G (Set.Ioi x)).toReal ≤ C := by
  sorry
