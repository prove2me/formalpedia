-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_absSqOp_apply_ne_zero
-- name    : GroundTheory.Automorphic.UnitaryRep.absSqOp_apply_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:33.837803+00:00
-- url     : https://prove2.me/theorems/4c0242e8-5215-43ff-a080-8cfd2ba627b0
-- title:
--   Unitary Rep: abs Sq Op apply ne zero
-- statement:
--   The Unitary Rep construction uses the abs Sq Op apply ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L42-L47

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

theorem GroundTheory.Automorphic.UnitaryRep.absSqOp_apply_ne_zero {f : G →₁[μ] ℂ} {v : H} (h : π.integrated μ f v ≠ 0) :
    π.absSqOp μ f v ≠ 0 := by sorry
