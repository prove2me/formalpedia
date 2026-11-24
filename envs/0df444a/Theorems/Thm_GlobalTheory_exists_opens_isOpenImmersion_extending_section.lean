-- Prove2me | Theorems.Thm_GlobalTheory_exists_opens_isOpenImmersion_extending_section
-- name    : GlobalTheory.exists_opens_isOpenImmersion_extending_section
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:41:53.928479+00:00
-- url     : https://prove2.me/theorems/3325e31c-2159-444b-a0e9-8d1431a387b1
-- title:
--   Global Theory: exists opens is Open Immersion extending section
-- statement:
--   The Global Theory construction uses the exists opens is Open Immersion extending section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDominantGeometricPointOfIsPreimmersion.lean#L51-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDominantGeometricPointOfIsPreimmersion.lean#L51-L74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDominantGeometricPointOfIsPreimmersion
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory

theorem GlobalTheory.exists_opens_isOpenImmersion_extending_section : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (Y : Scheme.{0}) (p : Y ⟶ X) (I : Type) [Finite I] (σ : I → (U ⟶ Y)), Etale p → IsSeparated p → (∀ i, σ i ≫ p = j) → (∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) (y : Sp k ⟶ Y), y ≫ p = u ≫ j → ∃ i, y = u ≫ σ i) → ∀ y : Y, ∃ (i : I) (W : Y.Opens), y ∈ W ∧ IsOpenImmersion (W.ι ≫ p) ∧ pullback.fst (W.ι ≫ p) j ≫ W.ι = pullback.snd (W.ι ≫ p) j ≫ σ i := by sorry
