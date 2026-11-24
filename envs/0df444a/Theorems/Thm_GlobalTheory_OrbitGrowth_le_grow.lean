-- Prove2me | Theorems.Thm_GlobalTheory_OrbitGrowth_le_grow
-- name    : GlobalTheory.OrbitGrowth.le_grow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:01.475612+00:00
-- url     : https://prove2.me/theorems/bec62b2c-c366-489d-9de6-4274840b3fc5
-- title:
--   Orbit Growth: le grow
-- statement:
--   The Orbit Growth construction uses the le grow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L65-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitGrowth
variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.OrbitGrowth.le_grow (A : Subalgebra ℂ (Module.End ℂ M)) (W : Submodule ℂ M) : W ≤ grow A W := by sorry
