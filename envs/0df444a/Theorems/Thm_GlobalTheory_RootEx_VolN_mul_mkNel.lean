-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_mul_mkNel
-- name    : GlobalTheory.RootEx.VolN.mul_mkNel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:48.03288+00:00
-- url     : https://prove2.me/theorems/dbde2a61-84b8-40b4-9eac-776530a9a60f
-- title:
--   Vol N: mul mk Nel
-- statement:
--   The Vol N construction uses the mul mk Nel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L174-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L174-L181

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.RootEx.VolN.mul_mkNel (p : ℕ) (g : N k n c p) (e : Ix n c p → k) :
    g * mkNel p e = mkNel p ((lm (Up n c p) (g : GL (n ⊕ Fin c) k).val).mulVec e + co p g) := by sorry
