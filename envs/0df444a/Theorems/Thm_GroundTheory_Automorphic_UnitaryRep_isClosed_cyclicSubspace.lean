-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isClosed_cyclicSubspace
-- name    : GroundTheory.Automorphic.UnitaryRep.isClosed_cyclicSubspace
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:48.773948+00:00
-- url     : https://prove2.me/theorems/6889bd9d-ebef-4bb8-b60f-fc00342b4234
-- title:
--   Unitary Rep: is Closed cyclic Subspace
-- statement:
--   The Unitary Rep construction uses the is Closed cyclic Subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L177-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L177-L178

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

theorem GroundTheory.Automorphic.UnitaryRep.isClosed_cyclicSubspace (v : H) : IsClosed (π.cyclicSubspace v : Set H) := by sorry
