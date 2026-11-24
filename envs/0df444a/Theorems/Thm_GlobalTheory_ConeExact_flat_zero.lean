-- Prove2me | Theorems.Thm_GlobalTheory_ConeExact_flat_zero
-- name    : GlobalTheory.ConeExact.flat_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:25:53.011945+00:00
-- url     : https://prove2.me/theorems/9387855b-fa8a-4983-b97b-17e579d7313e
-- title:
--   Cone Exact: flat zero
-- statement:
--   The Cone Exact construction uses the flat zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L174-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L174-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [CommRing R] {K : ℕ → Type v} {C : ℕ → Type w} [∀ p, AddCommGroup (K p)]
  [∀ p, AddCommGroup (C p)] [∀ p, Module R (K p)] [∀ p, Module R (C p)]
variable {dK : ∀ p, K p →ₗ[R] K (p + 1)} {dC : ∀ p, C p →ₗ[R] C (p + 1)}
    {φ : ∀ p, K p →ₗ[R] C p}

theorem GlobalTheory.ConeExact.flat_zero [∀ p, Module.Flat R (K (p + 1))] [∀ p, Module.Flat R (C p)]
    (h : ConeExact (fun p => dK p) (fun p => dC p) (fun p => φ p))
    (hK : ∀ p x, dK (p + 1) (dK p x) = 0) (hC : ∀ p x, dC (p + 1) (dC p x) = 0)
    (hφ : ∀ p x, dC p (φ p x) = φ (p + 1) (dK p x)) (n : ℕ)
    (hnK : ∀ p, n < p → Subsingleton (K p)) (hnC : ∀ p, n < p → Subsingleton (C p)) :
    Module.Flat R (K 0) := by sorry
