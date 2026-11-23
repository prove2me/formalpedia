-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_one_of_pow_eq_one
-- name    : GroundTheory.PAdicHodge.norm_eq_one_of_pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:29.624215+00:00
-- url     : https://prove2.me/theorems/0f36ca92-427b-442c-b589-e222cb7a4183
-- title:
--   PAdic Hodge: norm eq one of pow eq one
-- statement:
--   The PAdic Hodge construction uses the norm eq one of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L18-L21

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

theorem GroundTheory.PAdicHodge.norm_eq_one_of_pow_eq_one {x : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hx : x ^ N = 1) :
    ‖x‖ = 1 := by sorry
