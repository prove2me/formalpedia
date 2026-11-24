-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_conductor_exists
-- name    : GlobalTheory.SplitWeil.conductor_exists
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:45.904805+00:00
-- url     : https://prove2.me/theorems/53e659f9-da39-4e3a-8868-e39ae5a51f7f
-- title:
--   Split Weil: conductor exists
-- statement:
--   The Split Weil construction uses the conductor exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AddCharConductorAndHaarIntegersExist.lean#L78-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AddCharConductorAndHaarIntegersExist.lean#L78-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SplitWeil.conductor_exists :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [MeasurableSpace k] [BorelSpace k],
      (∀ ψ : AddChar k Circle, Continuous ψ → ψ ≠ 1 → ∃ c : kˣ, HasConductor ψ c) ∧
      (∃ ψ : AddChar k Circle, Continuous ψ ∧ ψ ≠ 1 ∧ HasConductor ψ 1) ∧
      ∃ ν : Measure k, IsUnitVol ν := by sorry
