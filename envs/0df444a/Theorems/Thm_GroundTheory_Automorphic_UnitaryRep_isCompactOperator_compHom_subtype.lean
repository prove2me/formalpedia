-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isCompactOperator_compHom_subtype
-- name    : GroundTheory.Automorphic.UnitaryRep.isCompactOperator_compHom_subtype
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:59:42.777532+00:00
-- url     : https://prove2.me/theorems/8131cafd-db81-4d03-a60e-96a506f19603
-- title:
--   Unitary Rep: is Compact Operator comp Hom subtype
-- statement:
--   The Unitary Rep construction uses the is Compact Operator comp Hom subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MultiplicityOne/OpenSubgroupRep.lean#L99-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MultiplicityOne/OpenSubgroupRep.lean#L99-L109

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_MultiplicityOne_OpenSubgroupRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology Function
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
set_option linter.unusedSectionVars false
variable [IsTopologicalGroup G] [T2Space G]
variable [MeasurableSpace G] [BorelSpace G]

theorem GroundTheory.Automorphic.UnitaryRep.isCompactOperator_compHom_subtype (π : UnitaryRep G H) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {L : Subgroup G} (hL : IsOpen (L : Set G))
    (hcpt : ∀ F : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ F)))
    (f : CompactlySupportedContinuousMap L ℂ) :
    haveI := isFiniteMeasureOnCompacts_comap μ hL
    IsCompactOperator ((π.compHom L.subtype continuous_subtype_val).integrated
      (μ.comap ((↑) : L → G)) (ccToL1 (μ.comap ((↑) : L → G)) f)) := by sorry
