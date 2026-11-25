-- Prove2me | Theorems.Thm_GlobalTheory_HL_encard_uniCosets_le
-- name    : GlobalTheory.HL.encard_uniCosets_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:34:41.184797+00:00
-- url     : https://prove2.me/theorems/53c138e7-b818-4928-ac3d-287223fb815b
-- title:
--   HL: encard uni Cosets le
-- statement:
--   The HL construction uses the encard uni Cosets le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardUniCosetsLe.lean#L184-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardUniCosetsLe.lean#L184-L193

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
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

theorem GlobalTheory.HL.encard_uniCosets_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (δ : E), δ ∈ L.O → IsUnit δ → ∀ N : ℕ, ({C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧ (∀ i j, δ * u i j ∈ L.O) ∧ C = {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}}.encard : ℝ≥0∞) ≤ (resQ ϖ : ℝ≥0∞) ^ ((vE L ϖ (δ * L.cj δ)).toNat * (N * (N - 1) / 2)) := by sorry
