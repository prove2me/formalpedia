-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_normB_symm
-- name    : GlobalTheory.WeylDuality.normB_symm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:50.314128+00:00
-- url     : https://prove2.me/theorems/e88e0cf7-9cc2-406f-8cb7-7911859adc4b
-- title:
--   Weyl Duality: norm B symm
-- statement:
--   The Weyl Duality construction uses the norm B symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L204-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L204-L205

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality

theorem GlobalTheory.WeylDuality.normB_symm {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : (normB hn ν).IsSymm := by sorry
