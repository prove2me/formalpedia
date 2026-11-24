-- Prove2me | Theorems.Thm_GlobalTheory_T_torus_inv_mul_pow_valuation_nonneg_iff
-- name    : GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:59:39.705352+00:00
-- url     : https://prove2.me/theorems/7646d9c2-d9a9-4a4f-9c57-6a6579bb8f94
-- title:
--   T: torus inv mul pow valuation nonneg iff
-- statement:
--   The T construction uses the torus inv mul pow valuation nonneg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorusInvMulPowValuationNonnegIffStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorusInvMulPowValuationNonnegIffStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusInvMulPowValuationNonnegIff
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValsAtApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusInvMulPowValuationNonnegIffStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.torus_inv_mul_pow_valuation_nonneg_iff : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ α : G, τ α = α → (∀ i, 0 < Multiplicative.toAdd (w i α)) → ∀ (t : T) (k : ℕ), (∀ i, 0 ≤ Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))) ↔ ∀ j, |Multiplicative.toAdd ((valsAt w e).comp T.subtype t) j| ≤ ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ) := by sorry
