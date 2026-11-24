-- Prove2me | Theorems.Thm_GlobalTheory_ZM_IsGaloisCover_of_isPullback
-- name    : GlobalTheory.ZM.IsGaloisCover.of_isPullback
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:29.928608+00:00
-- url     : https://prove2.me/theorems/5b4280a5-ebff-4d03-acb3-c2a9bbaec763
-- title:
--   Is Galois Cover: of is Pullback
-- statement:
--   The Is Galois Cover construction uses the of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GaloisCoverDescentAndCartesianSquares.lean#L170-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GaloisCoverDescentAndCartesianSquares.lean#L170-L204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GaloisCoverDescentAndCartesianSquares
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.IsGaloisCover
variable {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}
variable {X' Y' : Scheme.{0}} {π' : X' ⟶ Y'} {ρ' : Ga → (X' ⟶ X')} {u : X' ⟶ X} {v : Y' ⟶ Y}

theorem GlobalTheory.ZM.IsGaloisCover.of_isPullback (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v) (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (hπ : ∀ a, ρ' a ≫ π' = π') : IsGaloisCover Ga ρ' π' := by sorry
