-- Prove2me | Theorems.Thm_GlobalTheory_CompletePoint_formEq_mult
-- name    : GlobalTheory.CompletePoint.formEq_mult
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:32:10.039629+00:00
-- url     : https://prove2.me/theorems/efd65cb6-88cb-5538-a6a5-8f27d465cd21
-- title:
--   Complete Point: form Eq mult
-- statement:
--   The Complete Point construction uses the form Eq mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueTorusExtensionPointOfGroupPoint.lean#L134-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueTorusExtensionPointOfGroupPoint.lean#L134-L147

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTorusExtensionPointOfGroupPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompletePoint
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

theorem GlobalTheory.CompletePoint.formEq_mult {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ χ' : D.X) :
    FormEq (Sum.elim (DegPre.gtφT D T b (χ + χ')) fun k =>
        (lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b)).left ≫ thφ D.P.A (x3 D.P.A) k)
      (Sum.elim DegPre.gtε thε) (Sum.elim (DegPre.gtφT D T b χ) (DegPre.gtφT D T b χ'))
      (Sum.elim DegPre.gtε DegPre.gtε) := by sorry
