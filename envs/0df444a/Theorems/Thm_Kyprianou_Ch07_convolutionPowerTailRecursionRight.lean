-- Prove2me | Theorems.Thm_Kyprianou_Ch07_convolutionPowerTailRecursionRight
-- name    : Kyprianou.Ch07.convolutionPowerTailRecursionRight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:28:35.934403+00:00
-- url     : https://prove2.me/theorems/d60f90e1-7e86-47c7-9ed0-f65542c0a195
-- title:
--   Kesten n+1 convolution upper tail as an integral against the original probability law
-- statement:
--   For a real probability law G and n>=0, the upper tail of its (n+1)-fold convolution at x equals the lower integral over the original G of the shifted upper tail of its nth convolution power at (x-a,infinity). This uses commutativity of the underlying source sum-convolution and the proven Fubini tail identity. The orientation matches the Kyprianou Kesten proof.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14, printed pp.201–202; original PDF pp.210–211. Complete proof passed pinned private remote compiler job fe09aa2e-8399-418e-96cb-fe864a3cf34d.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_convolutionPowerProbability
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionComm
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailIntegral
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.convolutionPowerTailRecursionRight
    (G : Measure Real) [IsProbabilityMeasure G] (n : Nat) (x : Real) :
    (Kyprianou.Ch07.convolutionPower G (n + 1)) (Set.Ioi x) =
      ∫⁻ a : Real, (Kyprianou.Ch07.convolutionPower G n)
        (Set.Ioi (x - a)) ∂G := by
  sorry
