-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_absSqOp_self
-- name    : GroundTheory.Automorphic.UnitaryRep.inner_absSqOp_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:41:35.532166+00:00
-- url     : https://prove2.me/theorems/0db8ff33-2aa4-4ad2-b4a4-a5b1e039e37b
-- title:
--   Unitary Rep: inner abs Sq Op self
-- statement:
--   The Unitary Rep construction uses the inner abs Sq Op self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L38-L40

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

theorem GroundTheory.Automorphic.UnitaryRep.inner_absSqOp_self (f : G →₁[μ] ℂ) (v : H) :
    ⟪v, π.absSqOp μ f v⟫_ℂ = ⟪π.integrated μ f v, π.integrated μ f v⟫_ℂ := by sorry
