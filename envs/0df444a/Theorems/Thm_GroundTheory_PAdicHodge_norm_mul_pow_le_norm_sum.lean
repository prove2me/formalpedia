-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_mul_pow_le_norm_sum
-- name    : GroundTheory.PAdicHodge.norm_mul_pow_le_norm_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:54.948795+00:00
-- url     : https://prove2.me/theorems/6f654939-bb97-4fae-be3c-5f1c4c1af1e1
-- title:
--   PAdic Hodge: norm mul pow le norm sum
-- statement:
--   The PAdic Hodge construction uses the norm mul pow le norm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L274-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L274-L336

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

theorem GroundTheory.PAdicHodge.norm_mul_pow_le_norm_sum {k : ℕ} (hk : 1 ≤ k) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {b : ℕ → PadicAlgCl p} (hb : ∀ i, b i ∈ cycl p k) :
    ∀ i ∈ Finset.range p, ‖b i‖ * ‖ζ - 1‖ ^ i ≤ ‖∑ i ∈ Finset.range p, b i * (ζ - 1) ^ i‖ := by sorry
