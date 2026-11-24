-- Prove2me | Theorems.Thm_GlobalTheory_DivisibleHom_exists_factor
-- name    : GlobalTheory.DivisibleHom.exists_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:33.498265+00:00
-- url     : https://prove2.me/theorems/8542f74f-19bb-41d2-a72b-0e18b4374563
-- title:
--   Divisible Hom: exists factor
-- statement:
--   The Divisible Hom construction uses the exists factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L83-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L83-L107

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DivisibleHom
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}

theorem GlobalTheory.DivisibleHom.exists_factor {A B : Over S} [GrpObj A] [IsCommMonObj A]
    [GrpObj B] (M : ℕ)
    [QuasiCompact (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (u : A ⟶ B) [IsMonHom u] (hu : ∀ (T : Over S) (x : T ⟶ A), x ^ M = 1 → x ≫ u = 1) :
    ∃ φ : A ⟶ B, _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ = u := by sorry
