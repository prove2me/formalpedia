-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayConv_finite_idealsIn
-- name    : GlobalTheory.Hk.RayConv.finite_idealsIn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:34:58.107791+00:00
-- url     : https://prove2.me/theorems/d16fa598-0791-46a4-9f40-703506133c06
-- title:
--   Ray Conv: finite ideals In
-- statement:
--   The Ray Conv construction uses the finite ideals In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteIdealsIn.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteIdealsIn.lean#L73-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteIdealsIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayConv
variable {K : Type} [Field K] [NumberField K]
variable {M : ℕ} (D : RayData K M)

theorem GlobalTheory.Hk.RayConv.finite_idealsIn (g : D.G) (n : ℕ) : (idealsIn D g n).Finite := by sorry
