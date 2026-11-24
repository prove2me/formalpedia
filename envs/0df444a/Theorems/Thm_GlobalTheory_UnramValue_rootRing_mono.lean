-- Prove2me | Theorems.Thm_GlobalTheory_UnramValue_rootRing_mono
-- name    : GlobalTheory.UnramValue.rootRing_mono
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:01.93722+00:00
-- url     : https://prove2.me/theorems/52797698-5baf-4006-b1c1-1481442e4df1
-- title:
--   Unram Value: root Ring mono
-- statement:
--   The Unram Value construction uses the root Ring mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L24-L31

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

theorem GlobalTheory.UnramValue.rootRing_mono {m m' : ℕ} (h : m ∣ m') : rootRing l m ≤ rootRing l m' := by sorry
