-- Prove2me | Theorems.Thm_GlobalTheory_CovolumeOneSelfDual_finite_contributing
-- name    : GlobalTheory.CovolumeOneSelfDual.finite_contributing
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:40:27.026942+00:00
-- url     : https://prove2.me/theorems/16f6b496-c468-4345-a923-00df29506411
-- title:
--   Covolume One Self Dual: finite contributing
-- statement:
--   The Covolume One Self Dual construction uses the finite contributing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SelfDualOfCovolumeOne.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SelfDualOfCovolumeOne.lean#L36-L46

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierInversionZeroCompactQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SelfDualOfCovolumeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open GlobalTheory GlobalTheory.CovolumeOneSelfDual

theorem GlobalTheory.CovolumeOneSelfDual.finite_contributing {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] (Γ : AddSubgroup G) [DiscreteTopology Γ] {f : G → ℂ} (hs : HasCompactSupport f)
    {C : Set G} (hC : IsCompact C) : {γ : Γ | ∃ x ∈ C, f (γ + x) ≠ 0}.Finite := by sorry
