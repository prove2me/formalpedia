-- Prove2me | Theorems.Thm_GlobalTheory_NearlyPrimitive_norm_factorial_inv_le
-- name    : GlobalTheory.NearlyPrimitive.norm_factorial_inv_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:07.628299+00:00
-- url     : https://prove2.me/theorems/8729048f-abe3-4a82-878c-086b0842b1df
-- title:
--   Nearly Primitive: norm factorial inv le
-- statement:
--   The Nearly Primitive construction uses the norm factorial inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L34-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L34-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology
variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem GlobalTheory.NearlyPrimitive.norm_factorial_inv_le (p : ℕ) [hp : Fact p.Prime] (h : ‖(p : C)‖ = (p : ℝ)⁻¹) (n : ℕ) :
    ‖((n.factorial : C))⁻¹‖ ≤ ((p : ℝ) ^ (1 / ((p : ℝ) - 1))) ^ n := by sorry
