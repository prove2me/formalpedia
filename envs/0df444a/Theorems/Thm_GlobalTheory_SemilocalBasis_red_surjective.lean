-- Prove2me | Theorems.Thm_GlobalTheory_SemilocalBasis_red_surjective
-- name    : GlobalTheory.SemilocalBasis.red_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:53:32.865794+00:00
-- url     : https://prove2.me/theorems/708e5a74-ed2b-4b73-8f65-78a086e50ac1
-- title:
--   Semilocal Basis: red surjective
-- statement:
--   The Semilocal Basis construction uses the red surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsBasisMemOfSpanEqTopOfSemilocal.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsBasisMemOfSpanEqTopOfSemilocal.lean#L55-L61

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

theorem GlobalTheory.SemilocalBasis.red_surjective {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) : Function.Surjective (red e I) := by sorry
