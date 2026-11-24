-- Prove2me | Theorems.Thm_GlobalTheory_ThetaExh_Check_iso_append
-- name    : GlobalTheory.ThetaExh.Check.iso_append
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:08:34.482695+00:00
-- url     : https://prove2.me/theorems/4018fc6c-df96-4640-924f-fd3ac069f49d
-- title:
--   Check: iso append
-- statement:
--   The Check construction uses the iso append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/SplitLiftOfLiftParam.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/SplitLiftOfLiftParam.lean#L78-L85

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

theorem GlobalTheory.ThetaExh.Check.iso_append (S : List (Part A.CG)) (p : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [p]) w = A.lpSum (isoLoc N A S w) (spehLoc N A p w) := by sorry
