-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_isMulLeftInvariant_volGL
-- name    : GlobalTheory.SplitWeil.isMulLeftInvariant_volGL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:18.781291+00:00
-- url     : https://prove2.me/theorems/73c59cf2-9c5e-4272-ba36-8f6b3e8c688f
-- title:
--   Split Weil: is Mul Left Invariant vol GL
-- statement:
--   The Split Weil construction uses the is Mul Left Invariant vol GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsMulLeftInvariantVolGL.lean#L65-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsMulLeftInvariantVolGL.lean#L65-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem GlobalTheory.SplitWeil.isMulLeftInvariant_volGL : (volGL ν n).IsMulLeftInvariant := by sorry
