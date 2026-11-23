-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul_apply_succ
-- name    : GlobalTheory.RootEx.Radical.Uni.mul_apply_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:23.882803+00:00
-- url     : https://prove2.me/theorems/08a3e7f4-56cd-4c56-89fa-1a609eda6771
-- title:
--   Uni: mul apply succ
-- statement:
--   The Uni construction uses the mul apply succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L57-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L57-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.RootEx.Radical.Uni.mul_apply_succ {b : ι → ℕ} {M M' : Matrix ι ι k} (h : Uni b M) (h' : Uni b M')
    {r s : ι} (hrs : b s = b r + 1) : (M * M') r s = M r s + M' r s := by sorry
