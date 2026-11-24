-- Prove2me | Theorems.Thm_GlobalTheory_RootExSource_det_linPart
-- name    : GlobalTheory.RootExSource.det_linPart
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:29:38.170217+00:00
-- url     : https://prove2.me/theorems/140ecfd9-3b70-4994-b4cc-4b3c9ecaf984
-- title:
--   Root Ex Source: det lin Part
-- statement:
--   The Root Ex Source construction uses the det lin Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SecondCountableLocal.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SecondCountableLocal.lean#L97-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
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
open GlobalTheory GlobalTheory.RootExSource
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ}
open Classical

theorem GlobalTheory.RootExSource.det_linPart {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) : (linPart n p g).det = 1 := by sorry
