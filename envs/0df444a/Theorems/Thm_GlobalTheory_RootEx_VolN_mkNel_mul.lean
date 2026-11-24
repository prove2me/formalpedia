-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_mkNel_mul
-- name    : GlobalTheory.RootEx.VolN.mkNel_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:24.979796+00:00
-- url     : https://prove2.me/theorems/3f9f4c1f-1ba0-44f7-a355-91687e455263
-- title:
--   Vol N: mk Nel mul
-- statement:
--   The Vol N construction uses the mk Nel mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L183-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L183-L190

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

theorem GlobalTheory.RootEx.VolN.mkNel_mul (p : ℕ) (g : N k n c p) (e : Ix n c p → k) :
    mkNel p e * g = mkNel p ((rm (Up n c p) (g : GL (n ⊕ Fin c) k).val).mulVec e + co p g) := by sorry
