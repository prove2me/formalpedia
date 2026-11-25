-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_isRightAct_funPull
-- name    : GlobalTheory.LevDesc.isRightAct_funPull
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:58.568843+00:00
-- url     : https://prove2.me/theorems/22908bcd-5f8d-49d7-9b18-988de1819cb4
-- title:
--   Lev Desc: is Right Act fun Pull
-- statement:
--   The Lev Desc construction uses the is Right Act fun Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L26-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]

theorem GlobalTheory.LevDesc.isRightAct_funPull {Z : Type} [MulAction G Z] : IsRightAct (funPull K (Z := Z) (G := G)) := by sorry
