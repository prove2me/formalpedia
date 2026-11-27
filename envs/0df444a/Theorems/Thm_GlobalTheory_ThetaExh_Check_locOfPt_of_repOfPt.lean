-- Prove2me | Theorems.Thm_GlobalTheory_ThetaExh_Check_locOfPt_of_repOfPt
-- name    : GlobalTheory.ThetaExh.Check.locOfPt_of_repOfPt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:09.974973+00:00
-- url     : https://prove2.me/theorems/058f78e2-5e58-4b13-99df-e93dc2f19cf5
-- title:
--   Check: loc Of Pt of rep Of Pt
-- statement:
--   The Check construction uses the loc Of Pt of rep Of Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/SplitLiftOfLiftParam.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/SplitLiftOfLiftParam.lean#L25-L27

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

theorem GlobalTheory.ThetaExh.Check.locOfPt_of_repOfPt (i : N.Loc) (h : RepOfPt N A i) : LocOfPt N A i := by sorry
