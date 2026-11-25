-- Prove2me | Theorems.Thm_GlobalTheory_degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk
-- name    : GlobalTheory.degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:42:32.4658+00:00
-- url     : https://prove2.me/theorems/d3dbd2ae-6089-4f98-a3e9-6626d5e425de
-- title:
--   Global Theory: deg Pre abelian Part is Integral and is Integrally Closed stalk
-- statement:
--   The Global Theory construction uses the deg Pre abelian Part is Integral and is Integrally Closed stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/DegPreAbelianPartIsIntegralAndIsIntegrallyClosed.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/DegPreAbelianPartIsIntegralAndIsIntegrallyClosed.lean#L15-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_DegPreAbelianPartIsIntegralAndIsIntegrallyClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk :
    ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
      [Algebra (FractionRing R) F], IsIntegral (DegPre.BF D F).left ∧
        ∀ y : (DegPre.BF D F).left, IsIntegrallyClosed ((DegPre.BF D F).left.presheaf.stalk y) := by sorry
