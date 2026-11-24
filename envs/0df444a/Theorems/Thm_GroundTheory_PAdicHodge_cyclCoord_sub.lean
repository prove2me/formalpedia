-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cyclCoord_sub
-- name    : GroundTheory.PAdicHodge.cyclCoord_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:13.530389+00:00
-- url     : https://prove2.me/theorems/2f303779-c85f-4974-a85b-2fc5210b8fc1
-- title:
--   PAdic Hodge: cycl Coord sub
-- statement:
--   The PAdic Hodge construction uses the cycl Coord sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L467-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L467-L469

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

theorem GroundTheory.PAdicHodge.cyclCoord_sub (k : ℕ) (η y y' : PadicAlgCl p) (i : ℕ) :
    cyclCoord k η (y - y') i = cyclCoord k η y i - cyclCoord k η y' i := by sorry
