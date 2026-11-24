-- Prove2me | Theorems.Thm_GlobalTheory_FibreUnif_isHolTo_of_isPullback
-- name    : GlobalTheory.FibreUnif.isHolTo_of_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:23.885966+00:00
-- url     : https://prove2.me/theorems/31876d5e-98bd-4052-9d72-cf589655487e
-- title:
--   Fibre Unif: is Hol To of is Pullback
-- statement:
--   The Fibre Unif construction uses the is Hol To of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/FamilyUniformisationFibreTheta.lean#L23-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/FamilyUniformisationFibreTheta.lean#L23-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_FamilyUniformisationFibreTheta
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.FibreUnif

theorem GlobalTheory.FibreUnif.isHolTo_of_isPullback {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y Z : Scheme.{0}} {φ : Y ⟶ Z}
    {s : Y ⟶ Sp ℂ} {p : Z ⟶ X} {y : Sp ℂ ⟶ X} (H : IsPullback φ s p y) {e : V → (Sp ℂ ⟶ Y)}
    (hs : ∀ z, e z ≫ s = 𝟙 _) (hol : IsHolTo Set.univ (fun z => e z ≫ φ)) : IsHolTo Set.univ e := by sorry
