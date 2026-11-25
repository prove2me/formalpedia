-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_one_add_pow_ne_one
-- name    : GroundTheory.PAdicHodge.one_add_pow_ne_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:39.151947+00:00
-- url     : https://prove2.me/theorems/d12222c9-0b48-4bd3-b6be-d16d9e173483
-- title:
--   PAdic Hodge: one add pow ne one
-- statement:
--   The PAdic Hodge construction uses the one add pow ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L15-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L15-L93

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
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
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]

theorem GroundTheory.PAdicHodge.one_add_pow_ne_one {w : PadicAlgCl p} (hw0 : w ≠ 0) (hw : ‖w‖ < (p : ℝ)⁻¹) {m : ℕ}
    (hm : m ≠ 0) : (1 + w) ^ m ≠ 1 := by sorry
