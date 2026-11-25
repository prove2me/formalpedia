-- Prove2me | Theorems.Thm_GlobalTheory_HL_Inhab_isTermW_of_isSD
-- name    : GlobalTheory.HL.Inhab.isTermW_of_isSD
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:39:53.60082+00:00
-- url     : https://prove2.me/theorems/70752fbd-d90f-4e84-9f04-e18a4d8dddbb
-- title:
--   Inhab: is Term W of is SD
-- statement:
--   The Inhab construction uses the is Term W of is SD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L219-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L219-L237

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.Inhab.isTermW_of_isSD (Λ : Submodule L.O S.V) (hΛ : IsSD L S.Hm Λ)
    (hf1 : ∀ a, S.f a ∈ Λ) (hf2 : ∀ a, S.f' a ∈ Λ) (hs1 : ∀ j, S.es j ∈ Λ) (hs2 : ∀ j, S.es' j ∈ Λ)
    (hT : ((S.T⁻¹ : Fˣ) : F) ∈ 𝒪[F]) (hT' : ((S.T'⁻¹ : Fˣ) : F) ∈ 𝒪[F])
    (hth : ∀ b, S.InTh Λ (S.f' b - S.f b)) :
    S.IsTermW (innerOf S S.f S.es Λ, innerOf S S.f' S.es' Λ, S.graphOf Λ) Λ 1 1 := by sorry
