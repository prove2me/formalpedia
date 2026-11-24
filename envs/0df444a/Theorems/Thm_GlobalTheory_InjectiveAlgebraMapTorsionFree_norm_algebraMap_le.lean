-- Prove2me | Theorems.Thm_GlobalTheory_InjectiveAlgebraMapTorsionFree_norm_algebraMap_le
-- name    : GlobalTheory.InjectiveAlgebraMapTorsionFree.norm_algebraMap_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:18:50.22174+00:00
-- url     : https://prove2.me/theorems/f80cf49f-5a69-4d02-8774-06373bad081b
-- title:
--   Injective Algebra Map Torsion Free: norm algebra Map le
-- statement:
--   The Injective Algebra Map Torsion Free construction uses the norm algebra Map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOne.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOne.lean#L24-L26

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

theorem GlobalTheory.InjectiveAlgebraMapTorsionFree.norm_algebraMap_le (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (PadicAlgCl p) a‖ ≤ 1 := by sorry
