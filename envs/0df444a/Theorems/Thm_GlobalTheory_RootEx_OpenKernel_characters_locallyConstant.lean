-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_OpenKernel_characters_locallyConstant
-- name    : GlobalTheory.RootEx.OpenKernel.characters_locallyConstant
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:07.813001+00:00
-- url     : https://prove2.me/theorems/f677bc4a-1675-4348-aaa9-95ab3c2886b4
-- title:
--   Open Kernel: characters locally Constant
-- statement:
--   The Open Kernel construction uses the characters locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousCharactersLocallyConstantNonarchLocalF.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousCharactersLocallyConstantNonarchLocalF.lean#L26-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open Filter Topology
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpenKernel
open MeasureTheory ValuativeRel Matrix
open Filter Topology

theorem GlobalTheory.RootEx.OpenKernel.characters_locallyConstant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ μ : kˣ →* ℂˣ, Continuous μ → IsOpen (μ.ker : Set kˣ)) ∧ ∀ ψ : AddChar k Circle, Continuous ψ → IsLocallyConstant (fun x : k => (ψ x : ℂ)) := by sorry
