-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_exists_section_laurentSeries
-- name    : GlobalTheory.OnePoint.exists_section_laurentSeries
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:37:36.148071+00:00
-- url     : https://prove2.me/theorems/ae7386ff-5507-49c2-8f0e-bb77badd42aa
-- title:
--   One Point: exists section laurent Series
-- statement:
--   The One Point construction uses the exists section laurent Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L320-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L320-L325

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]

theorem GlobalTheory.OnePoint.exists_section_laurentSeries {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyQuasiFinite f] (x : Spec (.of K⸨X⸩) ⟶ F) (hx : x ≫ f = specAlg(K, K⸨X⸩)) :
    ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, K⸨X⸩) ≫ x₀ = x ∧ x₀ ≫ f = 𝟙 _ ∧
      ∀ x₁ : Spec (.of K) ⟶ F, specAlg(K, K⸨X⸩) ≫ x₁ = x → x₁ = x₀ := by sorry
