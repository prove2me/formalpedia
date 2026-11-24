-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFamily_eq_of_finite_of_closed_fibres
-- name    : GlobalTheory.ThetaFamily.eq_of_finite_of_closed_fibres
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:30.704946+00:00
-- url     : https://prove2.me/theorems/5d649fd0-1770-450d-bae7-f73f561e7ae6
-- title:
--   Theta Family: eq of finite of closed fibres
-- statement:
--   The Theta Family construction uses the eq of finite of closed fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfFiniteOfClosedFibres.lean#L98-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfFiniteOfClosedFibres.lean#L98-L110

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Metric Set
open scoped Topology
open GlobalTheory GlobalTheory.ThetaFamily

theorem GlobalTheory.ThetaFamily.eq_of_finite_of_closed_fibres {X Y : Type*} [TopologicalSpace X] {B : Set X} (hB : IsPreconnected B)
    {C : Set Y} (hC : C.Finite) (c : X → Y) (hc : ∀ b ∈ B, c b ∈ C)
    (h : ∀ k ∈ C, ∀ b ∈ B, b ∈ closure {b' ∈ B | c b' = k} → c b = k) : ∀ b ∈ B, ∀ b' ∈ B, c b = c b' := by sorry
