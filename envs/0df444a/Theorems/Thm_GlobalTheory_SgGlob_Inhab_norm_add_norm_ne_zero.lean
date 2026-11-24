-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_norm_add_norm_ne_zero
-- name    : GlobalTheory.SgGlob.Inhab.norm_add_norm_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:50.205104+00:00
-- url     : https://prove2.me/theorems/2c00d392-96d7-46a7-95cc-bee91dbc5ab2
-- title:
--   Inhab: norm add norm ne zero
-- statement:
--   The Inhab construction uses the norm add norm ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L416-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L416-L424

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
omit [NumberField E]

theorem GlobalTheory.SgGlob.Inhab.norm_add_norm_ne_zero (σ : E →+* E) (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x))
    {a : E} (ha : a ≠ 0) (b : E) : a * σ a + b * σ b ≠ 0 := by sorry
