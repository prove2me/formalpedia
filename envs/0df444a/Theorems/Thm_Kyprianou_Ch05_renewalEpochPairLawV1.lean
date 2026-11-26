-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalEpochPairLawV1
-- name    : Kyprianou.Ch05.renewalEpochPairLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T19:00:11.428336+00:00
-- url     : https://prove2.me/theorems/c3e76d4c-7b74-4a54-95ee-68092607f12c
-- title:
--   The current renewal epoch and next mark have product convolution law
-- statement:
--   The current renewal epoch and next mark have product convolution law
-- source:
--   Kyprianou (2006), Lemma 5.5

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Kyprianou.Ch05

open Classical in
theorem Kyprianou.Ch05.renewalEpochPairLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : ℕ → Omega → ℝ) (F : Measure ℝ)
    (hRenewal : IsRenewalEpochProcess P Z F) (n : ℕ) :
    P.map (fun w => (renewalEpoch Z n w,Z n w)) =
      (renewalConvolutionPower F n).prod F := by
  sorry
