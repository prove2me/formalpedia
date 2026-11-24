-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_OpenKernel_isLocallyConstant_coe_addChar
-- name    : GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:22:11.182284+00:00
-- url     : https://prove2.me/theorems/9e54909c-6a2c-41fa-bbb1-f7130c66e808
-- title:
--   Open Kernel: is Locally Constant coe add Char
-- statement:
--   The Open Kernel construction uses the is Locally Constant coe add Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousCharactersLocallyConstantNonarchLocalF.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousCharactersLocallyConstantNonarchLocalF.lean#L12-L21

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

theorem GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    IsLocallyConstant (fun x : k => (ψ x : ℂ)) := by sorry
