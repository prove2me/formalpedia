-- Prove2me | Theorems.Thm_GlobalTheory_TorsionLift_existsUnique_of_surjective
-- name    : GlobalTheory.TorsionLift.existsUnique_of_surjective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:03:42.568394+00:00
-- url     : https://prove2.me/theorems/62b23693-b65f-4a03-8e2c-1ef99ecc6315
-- title:
--   Torsion Lift: exists Unique of surjective
-- statement:
--   The Torsion Lift construction uses the exists Unique of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueOfIsAdicComplete.lean#L99-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueOfIsAdicComplete.lean#L99-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueOfIsAdicComplete
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionLift
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  [IsCommMonObj G] [Smooth G.hom]

theorem GlobalTheory.TorsionLift.existsUnique_of_surjective {A A' : Type} [CommRing A] [Algebra R A] [CommRing A']
    [Algebra R A'] (q : A →ₐ[R] A') (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
    {N : ℕ} (hN : IsUnit (N : A)) (y₀ : sp (R₀ := R) A' ⟶ G) (hy₀ : y₀ ^ N = 1) :
    ∃! y : sp A ⟶ G, y ^ N = 1 ∧ spMap q ≫ y = y₀ := by sorry
