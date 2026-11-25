-- Prove2me | Theorems.Thm_GlobalTheory_UnramValue_norm_rootRing
-- name    : GlobalTheory.UnramValue.norm_rootRing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:00.142719+00:00
-- url     : https://prove2.me/theorems/4c07d306-f6bc-44ec-a6c6-1c7464058980
-- title:
--   Unram Value: norm root Ring
-- statement:
--   The Unram Value construction uses the norm root Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L161-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L161-L191

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.UnramValue.norm_rootRing {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) {y : Om l} (hy : y ∈ rootRing l m)
    (h0 : y ≠ 0) : ∃ n : ℤ, ‖y‖ = (l : ℝ) ^ n := by sorry
