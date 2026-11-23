-- Prove2me | Theorems.Thm_GlobalTheory_RootExSource_mul_apply_of_inN
-- name    : GlobalTheory.RootExSource.mul_apply_of_inN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:44.806282+00:00
-- url     : https://prove2.me/theorems/976dda47-6740-4921-b479-69c9d69cacba
-- title:
--   Root Ex Source: mul apply of in N
-- statement:
--   The Root Ex Source construction uses the mul apply of in N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SecondCountableLocal.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SecondCountableLocal.lean#L28-L38

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

theorem GlobalTheory.RootExSource.mul_apply_of_inN {m : Type} {g : GL (n' ⊕ Fin c) k} (hg : InN p g)
    (x : Matrix m (n' ⊕ Fin c) k) (r : m) (s : n' ⊕ Fin c) :
    (x * g.val) r s = x r s + ∑ s', if lev p s' < lev p s then x r s' * g.val s' s else 0 := by sorry
