-- Prove2me | Theorems.Thm_GlobalTheory_SemilocalBasis_red_apply
-- name    : GlobalTheory.SemilocalBasis.red_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:45:47.658765+00:00
-- url     : https://prove2.me/theorems/3c89d7d8-171c-49e9-a269-87fb817e05be
-- title:
--   Semilocal Basis: red apply
-- statement:
--   The Semilocal Basis construction uses the red apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsBasisMemOfSpanEqTopOfSemilocal.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsBasisMemOfSpanEqTopOfSemilocal.lean#L51-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsBasisMemOfSpanEqTopOfSemilocal
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
open GlobalTheory
open GlobalTheory.SemilocalBasis
open scoped Pointwise

theorem GlobalTheory.SemilocalBasis.red_apply {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) (x : M) (j : Fin n) :
    red e I x j = Ideal.Quotient.mk I (e.repr x j) := by sorry
