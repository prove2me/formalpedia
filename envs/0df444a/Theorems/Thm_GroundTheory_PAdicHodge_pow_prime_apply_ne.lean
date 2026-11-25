-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_pow_prime_apply_ne
-- name    : GroundTheory.PAdicHodge.pow_prime_apply_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:56.256407+00:00
-- url     : https://prove2.me/theorems/bc7e9785-728d-4773-acd6-2a666162e566
-- title:
--   PAdic Hodge: pow prime apply ne
-- statement:
--   The PAdic Hodge construction uses the pow prime apply ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L612-L650
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L612-L650

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

theorem GroundTheory.PAdicHodge.pow_prime_apply_ne {k : ℕ} (hk : 2 ≤ k) (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1)))
    (hτη : τ η ≠ η) {η' : PadicAlgCl p} (hη' : IsPrimitiveRoot η' (p ^ (k + 1 + 1))) :
    (τ ^ p) η' ≠ η' := by sorry
