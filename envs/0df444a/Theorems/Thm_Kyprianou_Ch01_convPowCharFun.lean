-- Prove2me | Theorems.Thm_Kyprianou_Ch01_convPowCharFun
-- name    : Kyprianou.Ch01.convPowCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:48:17.773095+00:00
-- url     : https://prove2.me/theorems/d8415e29-cb57-4db8-94fa-d4c704981ffd
-- title:
--   Characteristic function of arbitrary IID convolution powers of a real probability law
-- statement:
--   For any real probability law μ and any natural-number convolution power n (including n=0), the characteristic function of its n-fold convolution equals the nth power of its characteristic function. This supports constructing the logarithmically weighted convolution-power Lévy intensity for Kyprianou Chapter 1 Exercise 1.2(ii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), IID random sum convolution powers.

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms
open MeasureTheory ProbabilityTheory Complex QueueingFundamentals.MG1
set_option autoImplicit false

theorem Kyprianou.Ch01.convPowCharFun
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (xi : ℝ) :
    charFun (QueueingFundamentals.MG1.convPow μ n) xi =
      (charFun μ xi) ^ n := by
  sorry
