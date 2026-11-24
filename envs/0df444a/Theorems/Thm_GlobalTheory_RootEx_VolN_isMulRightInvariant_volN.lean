-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_isMulRightInvariant_volN
-- name    : GlobalTheory.RootEx.VolN.isMulRightInvariant_volN
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:02.173349+00:00
-- url     : https://prove2.me/theorems/903a6869-a88d-4298-901c-ded8d9b0afb2
-- title:
--   Vol N: is Mul Right Invariant vol N
-- statement:
--   The Vol N construction uses the is Mul Right Invariant vol N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L437-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L437-L438

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

theorem GlobalTheory.RootEx.VolN.isMulRightInvariant_volN (p : ℕ) : (volN ν n c p).IsMulRightInvariant := by sorry
