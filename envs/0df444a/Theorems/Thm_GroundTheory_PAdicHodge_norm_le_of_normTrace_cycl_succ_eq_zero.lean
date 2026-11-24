-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_le_of_normTrace_cycl_succ_eq_zero
-- name    : GroundTheory.PAdicHodge.norm_le_of_normTrace_cycl_succ_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:25.862085+00:00
-- url     : https://prove2.me/theorems/c31f2d84-0384-4941-9f8d-48cc972e4aa1
-- title:
--   PAdic Hodge: norm le of norm Trace cycl succ eq zero
-- statement:
--   The PAdic Hodge construction uses the norm le of norm Trace cycl succ eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L526-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L526-L557

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

theorem GroundTheory.PAdicHodge.norm_le_of_normTrace_cycl_succ_eq_zero {k : ℕ} (hk : 1 ≤ k)
    (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hτ : ∀ x ∈ cycl p k, τ x = x)
    {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1))) (hτη : τ η ≠ η)
    {y : PadicAlgCl p} (hy : y ∈ cycl p (k + 1)) (h0 : normTrace (cycl p k) y = 0) :
    ‖y‖ ≤ (p : ℝ) ^ 2 * ‖τ y - y‖ := by sorry
