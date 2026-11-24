-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Radical_simpleSum_eq_zero
-- name    : GlobalTheory.RootEx.Radical.simpleSum_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:40.461325+00:00
-- url     : https://prove2.me/theorems/1577c989-59d2-41d7-996d-47230fc6d9e0
-- title:
--   Radical: simple Sum eq zero
-- statement:
--   The Radical construction uses the simple Sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L185-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L185-L193

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

theorem GlobalTheory.RootEx.Radical.simpleSum_eq_zero {g : GL (n ⊕ Fin c) k}
    (h : ∀ i j, g.val (Sum.inr i) (Sum.inr j) = (1 : Matrix (Fin c) (Fin c) k) i j) :
    simpleSum g = 0 := by sorry
