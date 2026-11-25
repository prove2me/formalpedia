-- Prove2me | Theorems.Thm_GlobalTheory_LB_isoOfGen_hom_app_genSec
-- name    : GlobalTheory.LB.isoOfGen_hom_app_genSec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:08:48.725353+00:00
-- url     : https://prove2.me/theorems/680e4442-8195-55e0-ae99-7c163c3b5226
-- title:
--   LB: iso Of Gen hom app gen Sec
-- statement:
--   The LB construction uses the iso Of Gen hom app gen Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/BijectiveSmulChartSec.lean#L609-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/BijectiveSmulChartSec.lean#L609-L622

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
variable (L : LB X)
variable {L}
variable {M : LB X}

theorem GlobalTheory.LB.isoOfGen_hom_app_genSec (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {a : LB.Gen L} {b : LB.Gen M} (ha : a.IsGen) (hb : b.IsGen) (h : LB.Gen.Maps w a b)
    (V : X.Opens) :
    (isoOfGen hL hM w hw).hom.app V (ofSec (DVR.genSec a ha) V) = ofSec (DVR.genSec b hb) V := by sorry
