-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_continuous_cycloChar
-- name    : GroundTheory.PAdicHodge.continuous_cycloChar
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:26.852047+00:00
-- url     : https://prove2.me/theorems/6fbee4da-6153-4d3c-9d5c-9e344085fa32
-- title:
--   PAdic Hodge: continuous cyclo Char
-- statement:
--   The PAdic Hodge construction uses the continuous cyclo Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateCpTwist.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateCpTwist.lean#L48-L49

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

theorem GroundTheory.PAdicHodge.continuous_cycloChar : Continuous (cycloChar K) := by sorry
