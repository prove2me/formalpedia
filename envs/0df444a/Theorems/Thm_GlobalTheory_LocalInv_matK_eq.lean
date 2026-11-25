-- Prove2me | Theorems.Thm_GlobalTheory_LocalInv_matK_eq
-- name    : GlobalTheory.LocalInv.matK_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:58.764148+00:00
-- url     : https://prove2.me/theorems/872e590b-d4b2-4ee1-affd-004b3a26a44f
-- title:
--   Local Inv: mat K eq
-- statement:
--   The Local Inv construction uses the mat K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L430-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L430-L434

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

theorem GlobalTheory.LocalInv.matK_eq (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om) :
    matK N i ρ g = algebraMap (N.O i) (Kf N i) ((N.chi i 1 g : (N.O i)ˣ) : N.O i) • matW N i ρ g := by sorry
