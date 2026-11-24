-- Prove2me | Theorems.Thm_GlobalTheory_Lin_mem_primesIoc_bounds
-- name    : GlobalTheory.Lin.mem_primesIoc_bounds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:06:53.561242+00:00
-- url     : https://prove2.me/theorems/4140ab48-b75a-430b-98cb-041e5c5e228b
-- title:
--   Lin: mem primes Ioc bounds
-- statement:
--   The Lin construction uses the mem primes Ioc bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumPrimesIocEqSumIndicator.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumPrimesIocEqSumIndicator.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPrimesIocEqSumIndicator
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

theorem GlobalTheory.Lin.mem_primesIoc_bounds {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {p : ℕ} (hp : p ∈ primesIoc x y) :
    x < p ∧ (p : ℝ) ≤ y := by sorry
