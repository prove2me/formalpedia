-- Prove2me | Theorems.Thm_GlobalTheory_CMNormIdentity_eq_zero_of_sum_embedding_smul
-- name    : GlobalTheory.CMNormIdentity.eq_zero_of_sum_embedding_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:14:48.867743+00:00
-- url     : https://prove2.me/theorems/65e953df-469c-4d28-a982-76136917534c
-- title:
--   CMNorm Identity: eq zero of sum embedding smul
-- statement:
--   The CMNorm Identity construction uses the eq zero of sum embedding smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfSumEmbeddingSmul.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfSumEmbeddingSmul.lean#L113-L116

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

theorem GlobalTheory.CMNormIdentity.eq_zero_of_sum_embedding_smul {E : Type} [Field E] [NumberField E] {g : ℕ} (f : (E →+* ℂ) → Fin g → ℂ)
    (hf : ∀ s : 𝓞 E, ∑ τ : E →+* ℂ, τ (s : E) • f τ = 0) (τ : E →+* ℂ) : f τ = 0 := by sorry
