-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_pos
-- name    : GroundTheory.PAdicHodge.cyclRadius_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:24.694032+00:00
-- url     : https://prove2.me/theorems/1edcd9d0-79a8-41e8-a6fe-bec5c2170ccc
-- title:
--   PAdic Hodge: cycl Radius pos
-- statement:
--   The PAdic Hodge construction uses the cycl Radius pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L223-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L223-L224

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

theorem GroundTheory.PAdicHodge.cyclRadius_pos (k : ℕ) : 0 < cyclRadius p (k + 1) := by sorry
