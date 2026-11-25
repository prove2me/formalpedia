-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isSymmetric_absSqOp
-- name    : GroundTheory.Automorphic.UnitaryRep.isSymmetric_absSqOp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:31:56.108284+00:00
-- url     : https://prove2.me/theorems/25856127-62e1-42a4-b11e-5f89b3f72e5f
-- title:
--   Unitary Rep: is Symmetric abs Sq Op
-- statement:
--   The Unitary Rep construction uses the is Symmetric abs Sq Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L35-L36

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

theorem GroundTheory.Automorphic.UnitaryRep.isSymmetric_absSqOp (f : G →₁[μ] ℂ) : (π.absSqOp μ f : H →ₗ[ℂ] H).IsSymmetric := by sorry
