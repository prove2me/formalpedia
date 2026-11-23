-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
-- name    : GlobalTheory.RootEx.Radical.Uni.inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:52.021189+00:00
-- url     : https://prove2.me/theorems/f80415dd-295f-4d88-81a7-b821fa7f77a0
-- title:
--   Uni: inv
-- statement:
--   The Uni construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L42-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L42-L55

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

theorem GlobalTheory.RootEx.Radical.Uni.inv {b : ι → ℕ} {g : GL ι k} (h : Uni b g.val) : Uni b (g⁻¹).val := by sorry
