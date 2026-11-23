-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_eq_of_isPrimitiveRoot
-- name    : GroundTheory.PAdicHodge.norm_sub_one_eq_of_isPrimitiveRoot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:12.830806+00:00
-- url     : https://prove2.me/theorems/2a3ff788-7b60-48cd-a816-cafd7f59862a
-- title:
--   PAdic Hodge: norm sub one eq of is Primitive Root
-- statement:
--   The PAdic Hodge construction uses the norm sub one eq of is Primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L33-L40

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

theorem GroundTheory.PAdicHodge.norm_sub_one_eq_of_isPrimitiveRoot {ζ η : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0)
    (hζ : IsPrimitiveRoot ζ N) (hη : IsPrimitiveRoot η N) : ‖η - 1‖ = ‖ζ - 1‖ := by sorry
