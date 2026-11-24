-- Prove2me | Theorems.Thm_GlobalTheory_T_continuous_characters_locallyConstant_nonarchLocalField
-- name    : GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:11.82211+00:00
-- url     : https://prove2.me/theorems/da276677-665b-4f33-b8e4-b9a9c836021b
-- title:
--   T: continuous characters locally Constant nonarch Local Field
-- statement:
--   The T construction uses the continuous characters locally Constant nonarch Local Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousCharactersLocallyConstantNonarchLocalFStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousCharactersLocallyConstantNonarchLocalFStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalFStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ μ : kˣ →* ℂˣ, Continuous μ → IsOpen (μ.ker : Set kˣ)) ∧ ∀ ψ : AddChar k Circle, Continuous ψ → IsLocallyConstant (fun x : k => (ψ x : ℂ)) := by sorry
