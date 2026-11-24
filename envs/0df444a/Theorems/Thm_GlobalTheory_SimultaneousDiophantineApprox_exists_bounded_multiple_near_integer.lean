-- Prove2me | Theorems.Thm_GlobalTheory_SimultaneousDiophantineApprox_exists_bounded_multiple_near_integer
-- name    : GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:12:14.478101+00:00
-- url     : https://prove2.me/theorems/06c5fbe0-94bf-4f37-9f7c-6993ece06c0a
-- title:
--   Simultaneous Diophantine Approx: exists bounded multiple near integer
-- statement:
--   The Simultaneous Diophantine Approx construction uses the exists bounded multiple near integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsBoundedMultipleNearInteger.lean#L57-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsBoundedMultipleNearInteger.lean#L57-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimultaneousDiophantineApprox
open NumberField

theorem GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer (E : Type) [Field E] [NumberField E] :
    ∃ M : ℕ, ∀ x : E, ∃ (m : ℕ) (y : E), 0 < m ∧ m ≤ M ∧ IsIntegral ℤ y ∧
      ‖canonicalEmbedding E ((m : E) * x - y)‖ < 1 := by sorry
