-- Prove2me | Theorems.Thm_GlobalTheory_HL_SAN_IntParam_finiteRing_sq_sub_mul_sq_eq_of_card
-- name    : GlobalTheory.HL.SAN.IntParam.finiteRing_sq_sub_mul_sq_eq_of_card
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:47:55.482533+00:00
-- url     : https://prove2.me/theorems/77f36bd6-2487-4154-a810-791ffc516e73
-- title:
--   Int Param: finite Ring sq sub mul sq eq of card
-- statement:
--   The Int Param construction uses the finite Ring sq sub mul sq eq of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianEichlerProductParamsIntegral.lean#L36-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianEichlerProductParamsIntegral.lean#L36-L103

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianEichlerProductParamsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SAN GlobalTheory.HL.SAN.IntParam
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.SAN.IntParam.finiteRing_sq_sub_mul_sq_eq_of_card (L : LocE F E) (N : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm)
    (hI : ∀ i j, Hm i j ∈ L.O) : ∀ (r : ℕ) (X Y u : Fin r → Fin N → E) (s : Fin r → E)
    (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i j, X i j ∈ L.O) → (∀ i j, Y i j ∈ L.O) →
    (∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) → (∀ a b, hf L Hm (X a) (X b) = 0) →
    (∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) →
    (∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) →
    (∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) →
    (∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O) →
    (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by sorry
