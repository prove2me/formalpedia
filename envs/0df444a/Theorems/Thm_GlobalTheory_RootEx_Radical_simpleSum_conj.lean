-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Radical_simpleSum_conj
-- name    : GlobalTheory.RootEx.Radical.simpleSum_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:39.911508+00:00
-- url     : https://prove2.me/theorems/0f36d0e5-7031-4706-a35e-dd540be76be8
-- title:
--   Radical: simple Sum conj
-- statement:
--   The Radical construction uses the simple Sum conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L137-L140

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

theorem GlobalTheory.RootEx.Radical.simpleSum_conj (x : GL n k) (g : GL (n ⊕ Fin c) k) :
    simpleSum (embX c x * g * (embX c x)⁻¹) = simpleSum g := by sorry
