-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_inf
-- name    : GroundTheory.Automorphic.UnitaryRep.IsInvariant.inf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:49.412584+00:00
-- url     : https://prove2.me/theorems/20b9f02c-e772-4a01-b7e3-9980716bcf4d
-- title:
--   Is Invariant: inf
-- statement:
--   The Is Invariant construction uses the inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L169-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L169-L171

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable {π μ}
omit [MeasurableSpace G] [OpensMeasurableSpace G]

theorem GroundTheory.Automorphic.UnitaryRep.IsInvariant.inf {U V : Submodule ℂ H} (hU : π.IsInvariant U) (hV : π.IsInvariant V) :
    π.IsInvariant (U ⊓ V) := by sorry
