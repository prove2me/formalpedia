-- Prove2me | Theorems.Thm_GlobalTheory_LevCover_exists_finite_mod
-- name    : GlobalTheory.LevCover.exists_finite_mod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:38.835942+00:00
-- url     : https://prove2.me/theorems/d3546b9c-3166-467b-991f-ca0c3bdd81a8
-- title:
--   Lev Cover: exists finite mod
-- statement:
--   The Lev Cover construction uses the exists finite mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RangeSubsetOfGeom.lean#L47-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RangeSubsetOfGeom.lean#L47-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {S : Scheme.{0}}

theorem GlobalTheory.LevCover.exists_finite_mod (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {n : ℕ} (hn : 0 < n) :
    ∃ (κ : Type) (_ : Finite κ) (q : M → κ), ∀ a a', q a = q a' → ∃ c, a' = a + n • c := by sorry
