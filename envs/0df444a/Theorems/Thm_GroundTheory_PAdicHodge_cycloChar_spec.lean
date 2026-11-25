-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cycloChar_spec
-- name    : GroundTheory.PAdicHodge.cycloChar_spec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:16.296835+00:00
-- url     : https://prove2.me/theorems/0c160516-95e9-4712-b636-199a0f0d995f
-- title:
--   PAdic Hodge: cyclo Char spec
-- statement:
--   The PAdic Hodge construction uses the cyclo Char spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateCpTwist.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateCpTwist.lean#L51-L53

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

theorem GroundTheory.PAdicHodge.cycloChar_spec (σ : Gal(PadicAlgCl p/K)) {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ p ^ n = 1) :
    σ ζ = ζ ^ ((cycloChar K σ : ℤ_[p]).toZModPow n).val := by sorry
