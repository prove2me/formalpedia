-- Prove2me | Theorems.Thm_GlobalTheory_UU_SchurComp_trPt_comp
-- name    : GlobalTheory.UU.SchurComp.trPt_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:11:37.617294+00:00
-- url     : https://prove2.me/theorems/4b4485bd-0730-49a4-bdb3-4383c434426f
-- title:
--   Schur Comp: tr Pt comp
-- statement:
--   The Schur Comp construction uses the tr Pt comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalRaw.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalRaw.lean#L113-L119

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalRaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.UU.SchurComp.trPt_comp (m m' : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F m ≫ DegPre.trPt D F m' = DegPre.trPt D F (m * m') := by sorry
