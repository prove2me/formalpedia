-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UniformLattices_perp_mem_nhds
-- name    : GlobalTheory.RootEx.UniformLattices.perp_mem_nhds
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:12:17.597779+00:00
-- url     : https://prove2.me/theorems/f539f93c-6e44-484c-851e-9439e7abf11a
-- title:
--   Uniform Lattices: perp mem nhds
-- statement:
--   The Uniform Lattices construction uses the perp mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenKerOfContinuous.lean#L144-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenKerOfContinuous.lean#L144-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UniformLattices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {m : Type} [Fintype m]
variable {ψ : AddChar k Circle}

theorem GlobalTheory.RootEx.UniformLattices.perp_mem_nhds (hψ : Continuous ψ) (L : Submodule 𝒪[k] (m → k)) (hL : L.IsLattice k) :
    (perp ψ L : Set (m → k)) ∈ 𝓝 (0 : m → k) := by sorry
