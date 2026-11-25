-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isCompactOperator_restrict_integrated
-- name    : GroundTheory.Automorphic.UnitaryRep.isCompactOperator_restrict_integrated
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:44.201654+00:00
-- url     : https://prove2.me/theorems/cfc693d4-2e61-4846-971b-22a7cbe15069
-- title:
--   Unitary Rep: is Compact Operator restrict integrated
-- statement:
--   The Unitary Rep construction uses the is Compact Operator restrict integrated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MultiplicityOne/OpenSubgroupRep.lean#L113-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MultiplicityOne/OpenSubgroupRep.lean#L113-L131

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

theorem GroundTheory.Automorphic.UnitaryRep.isCompactOperator_restrict_integrated {G : Type*} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (μ : Measure G) {V : Submodule ℂ H} [CompleteSpace V]
    (hV : IsClosed (V : Set H)) (hinv : π.IsInvariant V) (g : G →₁[μ] ℂ)
    (h : IsCompactOperator (π.integrated μ g)) :
    IsCompactOperator ((π.restrict V hinv).integrated μ g) := by sorry
