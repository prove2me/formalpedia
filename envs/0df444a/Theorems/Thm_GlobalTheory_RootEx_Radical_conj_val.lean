-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Radical_conj_val
-- name    : GlobalTheory.RootEx.Radical.conj_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:18.316317+00:00
-- url     : https://prove2.me/theorems/3466c93b-8b9c-4eb5-88a2-b9327455522a
-- title:
--   Radical: conj val
-- statement:
--   The Radical construction uses the conj val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L107-L114

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

theorem GlobalTheory.RootEx.Radical.conj_val (x : GL n k) (g : GL (n ⊕ Fin c) k) :
    (embX c x * g * (embX c x)⁻¹).val =
      fromBlocks (x.val * g.val.toBlocks₁₁ * (x⁻¹).val) (x.val * g.val.toBlocks₁₂)
        (g.val.toBlocks₂₁ * (x⁻¹).val) g.val.toBlocks₂₂ := by sorry
