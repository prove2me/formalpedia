-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_TargetUnip_linPart_mulVec
-- name    : GlobalTheory.RootEx.TargetUnip.linPart_mulVec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:30:13.976886+00:00
-- url     : https://prove2.me/theorems/0bd5908d-e953-490f-9e80-44fce68fc8d4
-- title:
--   Target Unip: lin Part mul Vec
-- statement:
--   The Target Unip construction uses the lin Part mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OpEOmTargetUnipotent.lean#L75-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OpEOmTargetUnipotent.lean#L75-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.TargetUnip
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
open Classical

theorem GlobalTheory.RootEx.TargetUnip.linPart_mulVec (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (a : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    (linPart p h).mulVec e a =
      ∑ r', h a.1.1 r' * (if hf : Free p (r', a.1.2) then e ⟨(r', a.1.2), hf⟩ else 0) := by sorry
