-- Prove2me | Theorems.Thm_GlobalTheory_CMNormIdentity_quadratic_eq_zero
-- name    : GlobalTheory.CMNormIdentity.quadratic_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:15:03.176691+00:00
-- url     : https://prove2.me/theorems/bed96ba6-e7a2-4652-893c-e5359d8e4a4b
-- title:
--   CMNorm Identity: quadratic eq zero
-- statement:
--   The CMNorm Identity construction uses the quadratic eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfSumEmbeddingSmul.lean#L118-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfSumEmbeddingSmul.lean#L118-L137

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingSmul
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
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CMNormIdentity

theorem GlobalTheory.CMNormIdentity.quadratic_eq_zero {L : Type} [AddCommGroup L] (B : L → L → ℂ) (hl : ∀ a b c, B (a + b) c = B a c + B b c)
    (hr : ∀ a b c, B a (b + c) = B a b + B a c) {m : ℕ} (e : Fin m → L)
    (he : Submodule.span ℤ (Set.range e) = ⊤) (h1 : ∀ i, B (e i) (e i) = 0)
    (h2 : ∀ i j, B (e i + e j) (e i + e j) = 0) (a : L) : B a a = 0 := by sorry
