-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_not_isUnit_natCast_normInteger
-- name    : GroundTheory.PAdicHodge.not_isUnit_natCast_normInteger
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:39.172826+00:00
-- url     : https://prove2.me/theorems/1b283300-742b-4377-ad15-78b8b198b48c
-- title:
--   PAdic Hodge: not is Unit nat Cast norm Integer
-- statement:
--   The PAdic Hodge construction uses the not is Unit nat Cast norm Integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L143-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L143-L158

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.not_isUnit_natCast_normInteger : ¬IsUnit (p : normInteger (PadicAlgCl p)) := by sorry
