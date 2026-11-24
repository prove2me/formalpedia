-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_isHaarMeasure_volN
-- name    : GlobalTheory.RootEx.VolN.isHaarMeasure_volN
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:08.734223+00:00
-- url     : https://prove2.me/theorems/6f8045bd-8dbf-415d-b3dc-513427f124bf
-- title:
--   Vol N: is Haar Measure vol N
-- statement:
--   The Vol N construction uses the is Haar Measure vol N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L427-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L427-L435

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem GlobalTheory.RootEx.VolN.isHaarMeasure_volN (p : ℕ) : (volN ν n c p).IsHaarMeasure := by sorry
