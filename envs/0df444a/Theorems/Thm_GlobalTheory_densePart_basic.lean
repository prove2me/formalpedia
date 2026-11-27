-- Prove2me | Theorems.Thm_GlobalTheory_densePart_basic
-- name    : GlobalTheory.densePart_basic
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:43.611536+00:00
-- url     : https://prove2.me/theorems/76dcae68-57dc-4bce-be1d-f74188ce1b3f
-- title:
--   Global Theory: dense Part basic
-- statement:
--   The Global Theory construction uses the dense Part basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoStalkMapOfFlatOfSurjectiveOnStalks.lean#L111-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoStalkMapOfFlatOfSurjectiveOnStalks.lean#L111-L116

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise

theorem GlobalTheory.densePart_basic : ∀ (X U : Scheme.{0}) (j : U ⟶ X), IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → genericPoints X ⊆ Set.range j ∧ (∀ u : U, IsIso (j.stalkMap u)) ∧ (IsReduced X → IsSchemeTheoreticallyDominant j) ∧ ∀ (Y : Scheme.{0}) (p : Y ⟶ X), UniversallyOpen p → IsDominant (pullback.fst p j) := by sorry
