-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_le_one
-- name    : GroundTheory.PAdicHodge.norm_sub_one_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:27.483084+00:00
-- url     : https://prove2.me/theorems/e747c08f-836a-40af-9091-a9e1f14cda49
-- title:
--   PAdic Hodge: norm sub one le one
-- statement:
--   The PAdic Hodge construction uses the norm sub one le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L60-L64

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

theorem GroundTheory.PAdicHodge.norm_sub_one_le_one {ζ : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hζ : ζ ^ N = 1) :
    ‖ζ - 1‖ ≤ 1 := by sorry
