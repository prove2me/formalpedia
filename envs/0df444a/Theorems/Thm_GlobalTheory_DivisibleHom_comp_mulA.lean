-- Prove2me | Theorems.Thm_GlobalTheory_DivisibleHom_comp_mulA
-- name    : GlobalTheory.DivisibleHom.comp_mulA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:22.041906+00:00
-- url     : https://prove2.me/theorems/3df0512c-7440-4628-89bd-11c575b59605
-- title:
--   Divisible Hom: comp mul A
-- statement:
--   The Divisible Hom construction uses the comp mul A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L66-L69

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

theorem GlobalTheory.DivisibleHom.comp_mulA {A T : Over S} [GrpObj A] (x : T ⟶ A) (n : ℕ) :
    x ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A n = x ^ n := by sorry
