-- Prove2me | Theorems.Thm_GlobalTheory_ThetaExh_Check_count_of_down
-- name    : GlobalTheory.ThetaExh.Check.count_of_down
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:39.852693+00:00
-- url     : https://prove2.me/theorems/a230b8a6-62ce-43d0-b784-dd5b9d0be755
-- title:
--   Check: count of down
-- statement:
--   The Check construction uses the count of down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/SplitLiftOfLiftParam.lean#L29-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/SplitLiftOfLiftParam.lean#L29-L40

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaExh GlobalTheory.ThetaExh.Check
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem GlobalTheory.ThetaExh.Check.count_of_down (i : N.Loc) (h1 : TypeNZ N A i) (h2 : DownMem N A i) : Count N A i := by sorry
