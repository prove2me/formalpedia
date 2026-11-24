-- Prove2me | Theorems.Thm_GlobalTheory_GelfandTrick_InDoubleCoset_mul
-- name    : GlobalTheory.GelfandTrick.InDoubleCoset.mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:53:45.743115+00:00
-- url     : https://prove2.me/theorems/3ae9bb5d-338c-4b00-8302-6c548070d8ab
-- title:
--   In Double Coset: mul
-- statement:
--   The In Double Coset construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetOperatorsCommOfAntiInvolution.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetOperatorsCommOfAntiInvolution.lean#L13-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
open GlobalTheory.GelfandTrick
variable {G : Type} [Group G]

theorem GlobalTheory.GelfandTrick.InDoubleCoset.mul {J : Subgroup G} {a y z j₁ j₂ : G} (h : InDoubleCoset J a y)
    (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J) (hz : z = j₁ * y * j₂) : InDoubleCoset J a z := by sorry
