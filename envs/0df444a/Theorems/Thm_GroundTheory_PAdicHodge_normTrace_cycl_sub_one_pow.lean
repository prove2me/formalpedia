-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_cycl_sub_one_pow
-- name    : GroundTheory.PAdicHodge.normTrace_cycl_sub_one_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:15.943374+00:00
-- url     : https://prove2.me/theorems/e6c2f289-d802-4a36-8220-011b0c33737f
-- title:
--   PAdic Hodge: norm Trace cycl sub one pow
-- statement:
--   The PAdic Hodge construction uses the norm Trace cycl sub one pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L338-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L338-L355

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

theorem GroundTheory.PAdicHodge.normTrace_cycl_sub_one_pow {k : ℕ} (hk : 1 ≤ k) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {i : ℕ} (hi : i < p) :
    normTrace (cycl p k) ((ζ - 1) ^ i) = (-1) ^ i := by sorry
