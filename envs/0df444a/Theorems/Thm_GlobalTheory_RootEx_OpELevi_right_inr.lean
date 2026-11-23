-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_OpELevi_right_inr
-- name    : GlobalTheory.RootEx.OpELevi.right_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:33.387378+00:00
-- url     : https://prove2.me/theorems/3de27aa6-82a5-4bd0-91c3-2b69abe50b89
-- title:
--   Op ELevi: right inr
-- statement:
--   The Op ELevi construction uses the right inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L109-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n] [DecidableEq n] [DecidableEq n']

theorem GlobalTheory.RootEx.OpELevi.right_inr (A : Matrix n' n' k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r s) :
    (x * (fromBlocks A 0 0 1 : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) r (Sum.inr s)
      = x r (Sum.inr s) := by sorry
