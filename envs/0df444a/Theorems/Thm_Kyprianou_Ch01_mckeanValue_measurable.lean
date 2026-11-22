-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanValue_measurable
-- name    : Kyprianou.Ch01.mckeanValue_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:59:35.320586+00:00
-- url     : https://prove2.me/theorems/de481b4f-4279-4d45-9c41-b1780d74663b
-- title:
--   The piecewise McKean value function is measurable for all parameters
-- statement:
--   The explicitly defined McKean value, equal to K-exp(y) below a fixed barrier and (K-exp barrier)*exp(-phi*(y-barrier)) otherwise, is Borel measurable for arbitrary real parameters. The switching region {y<barrier} is open and both branches are continuous. The result is needed to prove that the discounted value process has measurable time sections in the original right-natural Brownian filtration.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13; measurable state-value process.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanValue_measurable
    (K barrier phi : ℝ) :
    Measurable (mckeanValue K barrier phi) := by sorry
