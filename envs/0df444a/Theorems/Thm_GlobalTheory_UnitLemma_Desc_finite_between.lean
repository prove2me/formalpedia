-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_finite_between
-- name    : GlobalTheory.UnitLemma.Desc.finite_between
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:28:39.035645+00:00
-- url     : https://prove2.me/theorems/ffc9b4fc-57f6-42ac-a270-e262e3f06726
-- title:
--   Desc: finite between
-- statement:
--   The Desc construction uses the finite between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoPowLowerBoundSwappedPairs.lean#L13-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoPowLowerBoundSwappedPairs.lean#L13-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteIntegralClosureOfSeparableInvolutionAlgebrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoPowLowerBoundSwappedPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc

theorem GlobalTheory.UnitLemma.Desc.finite_between (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (R : Submodule O A) (hR : R.FG)
    (a : O) (ha : a ≠ 0) : Finite {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N} := by sorry
