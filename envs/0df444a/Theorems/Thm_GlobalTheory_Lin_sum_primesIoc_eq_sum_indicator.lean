-- Prove2me | Theorems.Thm_GlobalTheory_Lin_sum_primesIoc_eq_sum_indicator
-- name    : GlobalTheory.Lin.sum_primesIoc_eq_sum_indicator
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:07:12.116666+00:00
-- url     : https://prove2.me/theorems/d491873e-e9d3-4788-b453-299d52e80357
-- title:
--   Lin: sum primes Ioc eq sum indicator
-- statement:
--   The Lin construction uses the sum primes Ioc eq sum indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumPrimesIocEqSumIndicator.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumPrimesIocEqSumIndicator.lean#L13-L26

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

theorem GlobalTheory.Lin.sum_primesIoc_eq_sum_indicator (a : ℕ → ℂ) {x y t : ℝ} (ht : 0 ≤ t) (hty : t ≤ y) :
    ∑ p ∈ primesIoc x t, a p
      = ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) t := by sorry
