-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_pow_prime_pow_fix_and_move
-- name    : GroundTheory.PAdicHodge.pow_prime_pow_fix_and_move
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:27.498356+00:00
-- url     : https://prove2.me/theorems/49bbdad6-50d4-489c-b496-3eea6df57ba0
-- title:
--   PAdic Hodge: pow prime pow fix and move
-- statement:
--   The PAdic Hodge construction uses the pow prime pow fix and move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L652-L670
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L652-L670

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.pow_prime_pow_fix_and_move {n : ℕ} (hn : 2 ≤ n) (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hγn : ∀ x ∈ cycl p n, γ x = x) {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1)))
    (hγζ : γ ζ ≠ ζ) (j : ℕ) :
    (∀ x ∈ cycl p (n + j), (γ ^ (p ^ j)) x = x) ∧
      ∀ η : PadicAlgCl p, IsPrimitiveRoot η (p ^ (n + j + 1)) → (γ ^ (p ^ j)) η ≠ η := by sorry
