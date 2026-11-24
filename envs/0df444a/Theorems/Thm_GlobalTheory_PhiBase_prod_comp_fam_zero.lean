-- Prove2me | Theorems.Thm_GlobalTheory_PhiBase_prod_comp_fam_zero
-- name    : GlobalTheory.PhiBase.prod_comp_fam_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:06.013569+00:00
-- url     : https://prove2.me/theorems/77f47465-e8d2-43c8-b4b9-70e5ffeab942
-- title:
--   Phi Base: prod comp fam zero
-- statement:
--   The Phi Base construction uses the prod comp fam zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AbelianPartEqOfThetaOperatorEq.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AbelianPartEqOfThetaOperatorEq.lean#L44-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOfIsGenTransl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_DegPreAbelianPartIsIntegralAndIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsThetaPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitOfStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AbelianPartEqOfThetaOperatorEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PhiBase

theorem GlobalTheory.PhiBase.prod_comp_fam_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (t : DegPre.BF D F ⟶ DegPre.BF D F) {U : Type} [CommGroup U]
    (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (t.left ≫ DegPre.famφ D F 0 i) ^ DegPre.famε k i = h (t ≫ DegPre.prB D F).left ^ k := by sorry
