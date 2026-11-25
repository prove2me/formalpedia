-- Prove2me | Theorems.Thm_GlobalTheory_T_capelli_left_comatrix_qminor_eq
-- name    : GlobalTheory.T.capelli_left_comatrix_qminor_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:30:32.80739+00:00
-- url     : https://prove2.me/theorems/df313d28-e175-560c-85a4-9079f61d42ea
-- title:
--   T: capelli left comatrix qminor eq
-- statement:
--   The T construction uses the capelli left comatrix qminor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CapelliLeftComatrixStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CapelliLeftComatrixStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliLeftComatrix
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliLeftComatrixStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.capelli_left_comatrix_qminor_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (j l : Fin (m + 1)), ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) • (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) = if l = j then qdet E u else 0 := by sorry
