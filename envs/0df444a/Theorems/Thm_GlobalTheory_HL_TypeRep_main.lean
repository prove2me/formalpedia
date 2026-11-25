-- Prove2me | Theorems.Thm_GlobalTheory_HL_TypeRep_main
-- name    : GlobalTheory.HL.TypeRep.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:14:08.822197+00:00
-- url     : https://prove2.me/theorems/8ec72b89-a729-5aea-a9ec-56f1718e9794
-- title:
--   Type Rep: main
-- statement:
--   The Type Rep construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PairingSecondTypeTestOnRepresentatives.lean#L113-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PairingSecondTypeTestOnRepresentatives.lean#L113-L213

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingSecondTypeTestOnRepresentatives
import Theorems.Thm_GlobalTheory_FrameBasic_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TypeRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.TypeRep.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ¬ S.BBzero d Λ → ∀ B₀ : Set S.V, (∀ y ∈ B₀, y ∈ Λ ∧ y ∈ S.X ⊔ S.X') → (∀ y ∈ S.sat Λ, ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ) → (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', algebraMap F E S.th⁻¹ • (x₁ + x₁') ∈ B₀ → algebraMap F E S.th⁻¹ • (x₂ + x₂') ∈ B₀ → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) → S.TypeBe d Λ := by sorry
