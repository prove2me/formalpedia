-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cyclCoord_mem
-- name    : GroundTheory.PAdicHodge.cyclCoord_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:26.025295+00:00
-- url     : https://prove2.me/theorems/e179d7d1-bcc0-4aa3-93c4-5f446b2b96d3
-- title:
--   PAdic Hodge: cycl Coord mem
-- statement:
--   The PAdic Hodge construction uses the cycl Coord mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L460-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L460-L461

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

theorem GroundTheory.PAdicHodge.cyclCoord_mem (k : ℕ) (η y : PadicAlgCl p) (i : ℕ) : cyclCoord k η y i ∈ cycl p k := by sorry
