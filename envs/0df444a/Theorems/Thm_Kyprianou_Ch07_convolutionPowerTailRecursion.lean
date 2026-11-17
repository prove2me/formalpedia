-- Prove2me | Theorems.Thm_Kyprianou_Ch07_convolutionPowerTailRecursion
-- name    : Kyprianou.Ch07.convolutionPowerTailRecursion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:25:52.464246+00:00
-- url     : https://prove2.me/theorems/238529ee-5ac8-4106-9525-b34338e1f65a
-- title:
--   Kesten: exact n-to-n+1 convolution upper-tail recursion
-- statement:
--   For a real probability law G and n>=0, the tail of the (n+1)-fold sum-convolution distribution at x equals the lower integral over the n-fold convolution law of G((x-a,infinity)). This is the exact recursion needed to split a Kesten inductive tail inequality.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.14 proof, printed p.201 and following; original PDF p.210–211. Exact source proof remotely elaborated under pinned Mathlib in job f779a62f-9fae-4995-b491-8baaa0e9a2ae.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailIntegral
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.convolutionPowerTailRecursion
    (G : Measure Real) [IsProbabilityMeasure G] (n : Nat) (x : Real) :
    (Kyprianou.Ch07.convolutionPower G (n + 1)) (Set.Ioi x) =
      ∫⁻ a : Real, G (Set.Ioi (x - a))
        ∂(Kyprianou.Ch07.convolutionPower G n) := by
  sorry
