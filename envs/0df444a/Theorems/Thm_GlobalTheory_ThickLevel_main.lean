-- Prove2me | Theorems.Thm_GlobalTheory_ThickLevel_main
-- name    : GlobalTheory.ThickLevel.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:47:53.249889+00:00
-- url     : https://prove2.me/theorems/b25f384e-c0d9-45af-9120-6cc757625555
-- title:
--   Thick Level: main
-- statement:
--   The Thick Level construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalisedContentThickenedSetIndependentOfLevel.lean#L120-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalisedContentThickenedSetIndependentOfLevel.lean#L120-L254

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentBiUnionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalisedContentThickenedSetIndependentOfLevel
import Theorems.Thm_GlobalTheory_CardQuotientPow_main
import Theorems.Thm_GlobalTheory_QuotientCardinality_main

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
open GlobalTheory GlobalTheory.ThickLevel

theorem GlobalTheory.ThickLevel.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsHerm L Γ → IsUnit Γ.det → ∀ (Ω : Set (Fin m → Fin n → E)), (∀ y ∈ Ω, gramT L Hm y = Γ) → ∀ i i' : ℕ, 1 ≤ i → i ≤ i' → (∀ y ∈ Ω, ∀ A ∈ congK L ϖ m i, cT L A * Γ * A = Γ → rmul y A ∈ Ω) → IsCO (tupLat L Λs m) (thick L ϖ Ω i') → cont (tupLat L Λs m) (thick L ϖ Ω i) * cont (hermLat L m) (horb L ϖ Γ i') = cont (tupLat L Λs m) (thick L ϖ Ω i') * cont (hermLat L m) (horb L ϖ Γ i) := by sorry
