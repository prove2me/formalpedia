-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_sumOp_eq_sum_transversal
-- name    : GlobalTheory.FinWeil.sumOp_eq_sum_transversal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:44.835064+00:00
-- url     : https://prove2.me/theorems/2c64393a-489e-4d77-89f2-6aac3f9e7953
-- title:
--   Fin Weil: sum Op eq sum transversal
-- statement:
--   The Fin Weil construction uses the sum Op eq sum transversal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumOpTransversal.lean#L56-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumOpTransversal.lean#L56-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
open Classical
open scoped BigOperators
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.FinWeil.sumOp_eq_sum_transversal {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (A B : Submodule R X) (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) (v : M)
    (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) (ι : Type) [Fintype ι] (f : ι → X)
    (hf : ∀ i, f i ∈ B) (ht : ∀ b ∈ B, ∃! i, b - f i ∈ A) :
    _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ i, W (f i) v ∧
      _root_.GlobalTheory.FinWeil.idx A B = Fintype.card ι := by sorry
