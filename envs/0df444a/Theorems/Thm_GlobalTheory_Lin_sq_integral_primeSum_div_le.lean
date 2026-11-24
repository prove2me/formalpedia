-- Prove2me | Theorems.Thm_GlobalTheory_Lin_sq_integral_primeSum_div_le
-- name    : GlobalTheory.Lin.sq_integral_primeSum_div_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:07:13.829856+00:00
-- url     : https://prove2.me/theorems/3141807b-7e9e-4a0c-9f77-03ce081991c0
-- title:
--   Lin: sq integral prime Sum div le
-- statement:
--   The Lin construction uses the sq integral prime Sum div le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntervalIntegrableDivOfBounded.lean#L45-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntervalIntegrableDivOfBounded.lean#L45-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntervalIntegrableDivOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open scoped Classical

theorem GlobalTheory.Lin.sq_integral_primeSum_div_le (a : ℕ → ℂ) (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    (∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ / t) ^ 2 ≤
      Real.log (y / x) * ∫ t in x..y, ‖∑ p ∈ _root_.GlobalTheory.Lin.primesIoc x t, a p‖ ^ 2 / t := by sorry
