-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cyclCoord_zero
-- name    : GroundTheory.PAdicHodge.cyclCoord_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:40.9048+00:00
-- url     : https://prove2.me/theorems/8dcbbbe7-96ce-4782-a055-44429dccfb53
-- title:
--   PAdic Hodge: cycl Coord zero
-- statement:
--   The PAdic Hodge construction uses the cycl Coord zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L463-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L463-L465

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

theorem GroundTheory.PAdicHodge.cyclCoord_zero {k : ℕ} {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1)))
    (y : PadicAlgCl p) : cyclCoord k η y 0 = normTrace (cycl p k) y := by sorry
