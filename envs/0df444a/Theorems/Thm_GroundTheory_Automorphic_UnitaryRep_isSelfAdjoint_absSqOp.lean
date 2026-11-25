-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isSelfAdjoint_absSqOp
-- name    : GroundTheory.Automorphic.UnitaryRep.isSelfAdjoint_absSqOp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:54.613249+00:00
-- url     : https://prove2.me/theorems/9223b77f-fe49-40b9-8b32-78dbd2178708
-- title:
--   Unitary Rep: is Self Adjoint abs Sq Op
-- statement:
--   The Unitary Rep construction uses the is Self Adjoint abs Sq Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L32-L33

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

theorem GroundTheory.Automorphic.UnitaryRep.isSelfAdjoint_absSqOp (f : G →₁[μ] ℂ) : IsSelfAdjoint (π.absSqOp μ f) := by sorry
