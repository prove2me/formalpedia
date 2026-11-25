-- Prove2me | Theorems.Thm_GlobalTheory_UnramValue_isClosed_rootRing
-- name    : GlobalTheory.UnramValue.isClosed_rootRing
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:46:49.737331+00:00
-- url     : https://prove2.me/theorems/e873d6af-6f91-4985-878f-7db555f68a16
-- title:
--   Unram Value: is Closed root Ring
-- statement:
--   The Unram Value construction uses the is Closed root Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L60-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L60-L78

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

theorem GlobalTheory.UnramValue.isClosed_rootRing {m : ℕ} (hm : 0 < m) : IsClosed (rootRing l m : Set (Om l)) := by sorry
