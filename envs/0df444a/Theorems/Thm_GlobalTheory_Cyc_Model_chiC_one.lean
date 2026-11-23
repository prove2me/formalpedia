-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_Model_chiC_one
-- name    : GlobalTheory.Cyc.Model.chiC_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:57.774798+00:00
-- url     : https://prove2.me/theorems/7e3f46b3-5040-47fc-9071-b77bd8da336c
-- title:
--   Model: chi C one
-- statement:
--   The Model construction uses the chi C one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L241-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L241-L242

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

theorem GlobalTheory.Cyc.Model.chiC_one (σ : GQ l) : chiC chi 1 σ = (((chi σ : ℚ_[l]) : Om l) : PadicComplex l) := by sorry
