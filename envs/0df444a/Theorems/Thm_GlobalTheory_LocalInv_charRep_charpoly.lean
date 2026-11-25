-- Prove2me | Theorems.Thm_GlobalTheory_LocalInv_charRep_charpoly
-- name    : GlobalTheory.LocalInv.charRep_charpoly
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:06:17.235806+00:00
-- url     : https://prove2.me/theorems/57611f03-bf96-5fc1-9fdf-5929f6ae48de
-- title:
--   Local Inv: char Rep charpoly
-- statement:
--   The Local Inv construction uses the char Rep charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L135-L139

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem GlobalTheory.LocalInv.charRep_charpoly (i : N.Loc) (χ : G H.E N.Om →* (N.O i)ˣ) (g : G H.E N.Om) :
    ((charRep N i χ g : GL (Fin 1) (N.O i)) : Matrix (Fin 1) (Fin 1) (N.O i)).charpoly =
      X - C ((χ g : (N.O i)ˣ) : N.O i) := by sorry
