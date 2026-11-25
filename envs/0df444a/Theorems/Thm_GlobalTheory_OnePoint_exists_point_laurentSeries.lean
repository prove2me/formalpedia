-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_exists_point_laurentSeries
-- name    : GlobalTheory.OnePoint.exists_point_laurentSeries
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:41.549196+00:00
-- url     : https://prove2.me/theorems/a817a543-67eb-56d9-8886-17c208dd636c
-- title:
--   One Point: exists point laurent Series
-- statement:
--   The One Point construction uses the exists point laurent Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L327-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L327-L332

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

theorem GlobalTheory.OnePoint.exists_point_laurentSeries {X Y : Scheme.{u}} (κ : X ⟶ Y) [LocallyQuasiFinite κ]
    (x : Spec (.of K⸨X⸩) ⟶ X) (y : Spec (.of K) ⟶ Y) (hx : x ≫ κ = specAlg(K, K⸨X⸩) ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, K⸨X⸩) ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, K⸨X⸩) ≫ x₁ = x → x₁ = x₀ := by sorry
