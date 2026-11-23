-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Radical_colE_mem
-- name    : GlobalTheory.RootEx.Radical.colE_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:53.921172+00:00
-- url     : https://prove2.me/theorems/a3039650-37bb-4f12-b852-8654f2e8397b
-- title:
--   Radical: col E mem
-- statement:
--   The Radical construction uses the col E mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L206-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L206-L215

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
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.RootEx.Radical.colE_mem {i : ℕ} (β : n → k) (hi : p < i) : colE c i β ∈ N k n c p := by sorry
