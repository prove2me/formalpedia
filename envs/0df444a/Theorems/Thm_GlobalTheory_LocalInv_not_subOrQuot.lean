-- Prove2me | Theorems.Thm_GlobalTheory_LocalInv_not_subOrQuot
-- name    : GlobalTheory.LocalInv.not_subOrQuot
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:26:07.069811+00:00
-- url     : https://prove2.me/theorems/17fee9f6-cb4b-54e1-b39f-5029cdd28695
-- title:
--   Local Inv: not sub Or Quot
-- statement:
--   The Local Inv construction uses the not sub Or Quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L355-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L355-L428

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

theorem GlobalTheory.LocalInv.not_subOrQuot (eig : Eig N A) (hT : GlobalTheory.IndefiniteRowSideFullHecke.TemperedRepresentations.Tempered N A) (hLG : LocalGlobal N A)
    (hL : EigLaws N A eig) (hA : EigAway N A eig) (hAb : EigAbove N A eig) (hS : TemperedSizes N A eig)
    (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (x : N.X i) (π : A.CG R.r)
    (hx : HasParamX N A i x [⟨R.r, π, 1⟩]) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i))
    (hρ : IsRankPart N i x ρ) (w : PlE H) (j : ℕ) :
    ¬ SubOrQuot N i ρ (N.chi i 1 * eps N i ^ j) w := by sorry
