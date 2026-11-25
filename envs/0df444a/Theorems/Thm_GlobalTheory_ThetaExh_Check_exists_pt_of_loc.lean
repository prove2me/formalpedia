-- Prove2me | Theorems.Thm_GlobalTheory_ThetaExh_Check_exists_pt_of_loc
-- name    : GlobalTheory.ThetaExh.Check.exists_pt_of_loc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:52.950997+00:00
-- url     : https://prove2.me/theorems/29d07ade-4068-4c85-9f87-88c822e25373
-- title:
--   Check: exists pt of loc
-- statement:
--   The Check construction uses the exists pt of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/SplitLiftOfLiftParam.lean#L149-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/SplitLiftOfLiftParam.lean#L149-L161

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

theorem GlobalTheory.ThetaExh.Check.exists_pt_of_loc (i : N.Loc) (h : PtLocal N A i) (P P' : A.AV i) (x : N.X i)
    (hx : A.ptV i P' = some x) (hl : ∀ w, SplitOut N i w → A.locV i P w = A.locV i P' w) :
    ∃ y, A.ptV i P = some y ∧ ∀ w, SplitOut N i w → heckePol N i y w = heckePol N i x w := by sorry
