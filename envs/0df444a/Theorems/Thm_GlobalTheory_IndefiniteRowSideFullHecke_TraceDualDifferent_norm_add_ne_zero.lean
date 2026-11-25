-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TraceDualDifferent_norm_add_ne_zero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.norm_add_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:12.707516+00:00
-- url     : https://prove2.me/theorems/72f9d4a1-9955-5c81-ad8c-73a750d959df
-- title:
--   Trace Dual Different: norm add ne zero
-- statement:
--   The Trace Dual Different construction uses the norm add ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L91-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.norm_add_ne_zero {z : (F →+* ℝ) → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) (a : F) :
    ∏ τ : F →+* ℝ, (z τ + ((τ a : ℝ) : ℂ)) ≠ 0 := by sorry
