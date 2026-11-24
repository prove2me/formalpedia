-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_conj_mkNel
-- name    : GlobalTheory.RootEx.VolN.conj_mkNel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:29:52.435723+00:00
-- url     : https://prove2.me/theorems/a26acd96-bf8f-46fe-ad04-9b9d4b09be55
-- title:
--   Vol N: conj mk Nel
-- statement:
--   The Vol N construction uses the conj mk Nel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L223-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L223-L235

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

theorem GlobalTheory.RootEx.VolN.conj_mkNel (p : ℕ) (x : GL n k) (e : Ix n c p → k) :
    embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹ =
      (mkNel p ((rm (Up n c p) (embX c x⁻¹).val * lm (Up n c p) (embX c x).val).mulVec e) : N k n c p) := by sorry
