-- Prove2me | Theorems.Thm_GlobalTheory_LevCover_RepTors_clopenCond
-- name    : GlobalTheory.LevCover.RepTors.clopenCond
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:24.346072+00:00
-- url     : https://prove2.me/theorems/b1f7072c-3270-454a-9d04-9ce20bfd0874
-- title:
--   Rep Tors: clopen Cond
-- statement:
--   The Rep Tors construction uses the clopen Cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RangeSubsetOfGeom.lean#L77-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RangeSubsetOfGeom.lean#L77-L88

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

theorem GlobalTheory.LevCover.RepTors.clopenCond {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S}
    {et : La → (Z ⟶ G)} (R : RepTors G n La Z et) {T : Over S} (x y : La → (T ⟶ G))
    (hx : ∀ a c, x (a + c) = x a * x c) (hx' : ∀ a, x a ^ n = 1)
    (hy : ∀ a c, y (a + c) = y a * y c) (hy' : ∀ a, y a ^ n = 1) :
    ClopenCond T fun _ h => ∀ a, h ≫ x a = h ≫ y a := by sorry
