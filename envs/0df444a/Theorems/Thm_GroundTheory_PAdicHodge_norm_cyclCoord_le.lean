-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_cyclCoord_le
-- name    : GroundTheory.PAdicHodge.norm_cyclCoord_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:13.602797+00:00
-- url     : https://prove2.me/theorems/0a9e0f3a-e1fd-4c14-a084-d9ff02a7233c
-- title:
--   PAdic Hodge: norm cycl Coord le
-- statement:
--   The PAdic Hodge construction uses the norm cycl Coord le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L503-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L503-L509

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

theorem GroundTheory.PAdicHodge.norm_cyclCoord_le {k : ℕ} (hk : 1 ≤ k) {η : PadicAlgCl p}
    (hη : IsPrimitiveRoot η (p ^ (k + 1))) {y : PadicAlgCl p} (hy : y ∈ cycl p (k + 1)) (i : ℕ) :
    ‖cyclCoord k η y i‖ ≤ p * ‖y‖ := by sorry
