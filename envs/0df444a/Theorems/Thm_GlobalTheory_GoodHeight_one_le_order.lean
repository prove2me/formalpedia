-- Prove2me | Theorems.Thm_GlobalTheory_GoodHeight_one_le_order
-- name    : GlobalTheory.GoodHeight.one_le_order
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:55.594778+00:00
-- url     : https://prove2.me/theorems/5fb9b53f-3ff9-498f-a009-ba01a0ee6e7e
-- title:
--   Good Height: one le order
-- statement:
--   The Good Height construction uses the one le order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBoundRight.lean#L50-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBoundRight.lean#L50-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GoodHeight

theorem GlobalTheory.GoodHeight.one_le_order {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {w : ℂ} (h1 : w ≠ 1)
    (hw : LFunction χ w = 0) : 1 ≤ analyticOrderNatAt (LFunction χ) w := by sorry
