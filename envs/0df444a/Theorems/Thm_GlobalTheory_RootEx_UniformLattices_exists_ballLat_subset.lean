-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UniformLattices_exists_ballLat_subset
-- name    : GlobalTheory.RootEx.UniformLattices.exists_ballLat_subset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:49.199693+00:00
-- url     : https://prove2.me/theorems/7becdb69-f2fe-46ca-8b64-e048a62d9a34
-- title:
--   Uniform Lattices: exists ball Lat subset
-- statement:
--   The Uniform Lattices construction uses the exists ball Lat subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenKerOfContinuous.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenKerOfContinuous.lean#L112-L117

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

theorem GlobalTheory.RootEx.UniformLattices.exists_ballLat_subset {V : Set (m → k)} (hV : V ∈ 𝓝 (0 : m → k)) :
    ∃ s : kˣ, (ballLat m s : Set (m → k)) ⊆ V := by sorry
