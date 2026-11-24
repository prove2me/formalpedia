-- Prove2me | Theorems.Thm_GlobalTheory_InjectiveAlgebraMapTorsionFree_norm_le_one_of_isIntegral
-- name    : GlobalTheory.InjectiveAlgebraMapTorsionFree.norm_le_one_of_isIntegral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:18:52.831452+00:00
-- url     : https://prove2.me/theorems/060a9a70-acf7-4fc1-b1bc-d31709dd8fa1
-- title:
--   Injective Algebra Map Torsion Free: norm le one of is Integral
-- statement:
--   The Injective Algebra Map Torsion Free construction uses the norm le one of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOne.lean#L28-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOne.lean#L28-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InjectiveAlgebraMapTorsionFree
variable (p : ℕ) [Fact (Nat.Prime p)]

theorem GlobalTheory.InjectiveAlgebraMapTorsionFree.norm_le_one_of_isIntegral (x : PadicAlgCl p) (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by sorry
