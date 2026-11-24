-- Prove2me | Theorems.Thm_GlobalTheory_NormPowerTwoUnity_norm_sq_sub_one_ge
-- name    : GlobalTheory.NormPowerTwoUnity.norm_sq_sub_one_ge
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:35:59.182804+00:00
-- url     : https://prove2.me/theorems/a7881c34-7dd1-471f-952f-9cf5632a0feb
-- title:
--   Norm Power Two Unity: norm sq sub one ge
-- statement:
--   The Norm Power Two Unity construction uses the norm sq sub one ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EqOneOfNormPowTwoPowSubOneLt.lean#L5-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EqOneOfNormPowTwoPowSubOneLt.lean#L5-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_EqOneOfNormPowTwoPowSubOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormPowerTwoUnity

theorem GlobalTheory.NormPowerTwoUnity.norm_sq_sub_one_ge (w : ℂ) (h : ‖w - 1‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by sorry
