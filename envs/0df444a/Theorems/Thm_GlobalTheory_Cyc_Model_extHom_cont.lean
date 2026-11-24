-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_Model_extHom_cont
-- name    : GlobalTheory.Cyc.Model.extHom_cont
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:34:18.932808+00:00
-- url     : https://prove2.me/theorems/f7cf8adc-f28b-4b19-82d9-c829df6b27ee
-- title:
--   Model: ext Hom cont
-- statement:
--   The Model construction uses the ext Hom cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L27-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L27-L27

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.Model.extHom_cont (g : GQ l) : Continuous (extHom g) := by sorry
