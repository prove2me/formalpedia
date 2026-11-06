-- Prove2me | Theorems.Thm_OAI_SevenEighths_Detector_complex_simultaneous_saturation
-- name    : OAI.SevenEighths.Detector.complex_simultaneous_saturation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:54:03.214928+00:00
-- url     : https://prove2.me/theorems/7b2aaab6-2ae4-4875-9db4-5b761ea4a83c
-- title:
--   Detector: complex simultaneous saturation
-- statement:
--   The Detector construction uses the complex simultaneous saturation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector.lean#L117-L127
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector.lean#L117-L127

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Detector

theorem OAI.SevenEighths.Detector.complex_simultaneous_saturation {U δ r m ε : ℝ} {M S : ℂ}
    (hU : 1 < U) (hδ : (1 / 50 : ℝ) ≤ δ) (hε : 0 ≤ ε)
    (hprod : U ^ (δ * (r + m) - ε) ≤ ‖M * S‖ ^ 2)
    (hupperM : ‖M‖ ^ 2 ≤ U ^ (δ * r + ε))
    (hupperS : ‖S‖ ^ 2 ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε ∧
      U ^ (δ * r - 2 * ε) ≤ ‖M‖ ^ 2 ∧
      U ^ (δ * m - 2 * ε) ≤ ‖S‖ ^ 2 := by sorry
