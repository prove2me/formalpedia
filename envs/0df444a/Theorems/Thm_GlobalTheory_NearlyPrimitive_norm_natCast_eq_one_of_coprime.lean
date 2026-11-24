-- Prove2me | Theorems.Thm_GlobalTheory_NearlyPrimitive_norm_natCast_eq_one_of_coprime
-- name    : GlobalTheory.NearlyPrimitive.norm_natCast_eq_one_of_coprime
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:56.07181+00:00
-- url     : https://prove2.me/theorems/87eaac4f-e7fc-400c-9b58-f587047b1a28
-- title:
--   Nearly Primitive: norm nat Cast eq one of coprime
-- statement:
--   The Nearly Primitive construction uses the norm nat Cast eq one of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L13-L32

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

theorem GlobalTheory.NearlyPrimitive.norm_natCast_eq_one_of_coprime {p m : ℕ} (hp : ‖(p : C)‖ < 1) (h : Nat.Coprime p m) :
    ‖(m : C)‖ = 1 := by sorry
