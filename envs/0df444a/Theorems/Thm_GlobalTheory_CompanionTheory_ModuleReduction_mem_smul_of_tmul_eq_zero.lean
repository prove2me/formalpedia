-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ModuleReduction_mem_smul_of_tmul_eq_zero
-- name    : GlobalTheory.CompanionTheory.ModuleReduction.mem_smul_of_tmul_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:17.18261+00:00
-- url     : https://prove2.me/theorems/349e9d87-d753-49f4-a618-825451f3b345
-- title:
--   Module Reduction: mem smul of tmul eq zero
-- statement:
--   The Module Reduction construction uses the mem smul of tmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/MemSmulOfTmulEqZero.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/MemSmulOfTmulEqZero.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_MemSmulOfTmulEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct ChangeOfRings
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ModuleReduction

theorem GlobalTheory.CompanionTheory.ModuleReduction.mem_smul_of_tmul_eq_zero {A Q N : Type} [CommRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup N] [Module A N] (g : A →ₗ[A] Q) (hg : Function.Surjective g) (ξ : A)
    (hk : ∀ a, g a = 0 ↔ ∃ b, a = ξ * b) (m : N) (h : g 1 ⊗ₜ[A] m = 0) :
    ∃ n : N, m = ξ • n := by sorry
