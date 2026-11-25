-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_algebraMap_intermediateField_cp
-- name    : GroundTheory.PAdicHodge.algebraMap_intermediateField_cp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:14:47.528663+00:00
-- url     : https://prove2.me/theorems/a41d17ec-9c10-5fb8-add6-28cb718b1b8f
-- title:
--   PAdic Hodge: algebra Map intermediate Field cp
-- statement:
--   The PAdic Hodge construction uses the algebra Map intermediate Field cp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateCpTwist.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateCpTwist.lean#L21-L22

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
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
open UniformSpace
variable {p : ℕ} [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem GroundTheory.PAdicHodge.algebraMap_intermediateField_cp (k : K) :
    algebraMap K ℂ_[p] k = ((k : PadicAlgCl p) : ℂ_[p]) := by sorry
