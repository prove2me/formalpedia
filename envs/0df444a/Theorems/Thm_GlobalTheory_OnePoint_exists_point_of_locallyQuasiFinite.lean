-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_exists_point_of_locallyQuasiFinite
-- name    : GlobalTheory.OnePoint.exists_point_of_locallyQuasiFinite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:37:57.237799+00:00
-- url     : https://prove2.me/theorems/35b324ea-d101-421b-b2b5-a714c7ef27fe
-- title:
--   One Point: exists point of locally Quasi Finite
-- statement:
--   The One Point construction uses the exists point of locally Quasi Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L308-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L308-L318

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

theorem GlobalTheory.OnePoint.exists_point_of_locallyQuasiFinite {X Y : Scheme.{u}} (κ : X ⟶ Y)
    [LocallyQuasiFinite κ] (L : Type u) [Field L] [Algebra K L] [IsIntegrallyClosedIn K L]
    (x : Spec (.of L) ⟶ X) (y : Spec (.of K) ⟶ Y) (hx : x ≫ κ = specAlg(K, L) ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, L) ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, L) ≫ x₁ = x → x₁ = x₀ := by sorry
