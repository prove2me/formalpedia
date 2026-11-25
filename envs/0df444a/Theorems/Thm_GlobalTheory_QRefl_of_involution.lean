-- Prove2me | Theorems.Thm_GlobalTheory_QRefl_of_involution
-- name    : GlobalTheory.QRefl.of_involution
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:47:06.632857+00:00
-- url     : https://prove2.me/theorems/b16974bc-494c-5309-8363-d9b4829dd1c2
-- title:
--   QRefl: of involution
-- statement:
--   The QRefl construction uses the of involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/QuasiReflectionStabilizesLattice.lean#L110-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/QuasiReflectionStabilizesLattice.lean#L110-L156

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLattice
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
open GlobalTheory GlobalTheory.QRefl
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.QRefl.of_involution (hH : IsHerm L Hm) (c : (Fin n → E) →+ (Fin n → E))
    (hs : ∀ t v, c (t • v) = L.cj t • c v) (hc : ∀ v, c (c v) = v)
    (hf' : ∀ v w, hf L Hm (c v) (c w) = L.cj (hf L Hm v w))
    (Y : Submodule E (Fin n → E)) (hY : ∀ v ∈ Y, c v ∈ Y)
    (Λ : Submodule L.O (Fin n → E)) (hΛ : ∀ v ∈ Λ, c v ∈ Λ)
    (a : Fin n → E) (ha : c a = a) (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (hg : IsQRefl L Hm a g) :
    ∃ α : ((Fin n → E) ≃ₗ[E] (Fin n → E)) ≃* ((Fin n → E) ≃ₗ[E] (Fin n → E)),
      (fixG L Hm Y ⊓ stabL L Λ).map α.toMonoidHom = fixG L Hm Y ⊓ stabL L Λ ∧ α g = g⁻¹ := by sorry
