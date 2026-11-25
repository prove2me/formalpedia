-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isIrreducible_restrict_of_isMinimal
-- name    : GroundTheory.Automorphic.UnitaryRep.isIrreducible_restrict_of_isMinimal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:41:12.722126+00:00
-- url     : https://prove2.me/theorems/f407c045-2a98-46e8-b34a-8ecde3f62eac
-- title:
--   Unitary Rep: is Irreducible restrict of is Minimal
-- statement:
--   The Unitary Rep construction uses the is Irreducible restrict of is Minimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L137-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DiscreteSpectrumAbstract.lean#L137-L165

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

theorem GroundTheory.Automorphic.UnitaryRep.isIrreducible_restrict_of_isMinimal {V : Submodule ℂ H} [CompleteSpace V]
    (hV : π.IsInvariant V) (h : π.IsMinimal V) : (π.restrict V hV).IsIrreducible := by sorry
