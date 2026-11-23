-- Prove2me | Theorems.Thm_GlobalTheory_SymmetricSemicharacter_ex_neg_left
-- name    : GlobalTheory.SymmetricSemicharacter.ex_neg_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:21.700579+00:00
-- url     : https://prove2.me/theorems/958b5838-aa57-4bf1-94fe-e07c2bb2d032
-- title:
--   Symmetric Semicharacter: ex neg left
-- statement:
--   The Symmetric Semicharacter construction uses the ex neg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SemicharacterSqEqOneOfSymmetric.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SemicharacterSqEqOneOfSymmetric.lean#L68-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.SymmetricSemicharacter
open CubeValues
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem GlobalTheory.SymmetricSemicharacter.ex_neg_left (z : Fin g → ℂ) :
    (u.ex z).left ≫ (GrpObj.inv : A ⟶ A).left = (u.ex (-z)).left := by sorry
