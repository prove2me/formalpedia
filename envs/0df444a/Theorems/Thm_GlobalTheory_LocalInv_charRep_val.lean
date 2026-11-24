-- Prove2me | Theorems.Thm_GlobalTheory_LocalInv_charRep_val
-- name    : GlobalTheory.LocalInv.charRep_val
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:23:03.675923+00:00
-- url     : https://prove2.me/theorems/7eeb3869-20d1-4269-a462-6e6dc6569362
-- title:
--   Local Inv: char Rep val
-- statement:
--   The Local Inv construction uses the char Rep val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L131-L133

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

theorem GlobalTheory.LocalInv.charRep_val (i : N.Loc) (χ : G H.E N.Om →* (N.O i)ˣ) (g : G H.E N.Om) :
    ((charRep N i χ g : GL (Fin 1) (N.O i)) : Matrix (Fin 1) (Fin 1) (N.O i)) =
      Matrix.scalar (Fin 1) ((χ g : (N.O i)ˣ) : N.O i) := by sorry
