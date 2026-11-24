-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_coeff_subst_sumFamily_mem
-- name    : GlobalTheory.FormalInv.coeff_subst_sumFamily_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:34:33.190742+00:00
-- url     : https://prove2.me/theorems/be9b7b5b-0894-42f2-a26b-1212a1106004
-- title:
--   Formal Inv: coeff subst sum Family mem
-- statement:
--   The Formal Inv construction uses the coeff subst sum Family mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L592-L614
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L592-L614

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable {σ' τ' : Type*}

theorem GlobalTheory.FormalInv.coeff_subst_sumFamily_mem [Finite σ] [Finite σ'] [Finite τ] [Finite τ'] {S : Subring R}
    {g g' : ℕ} {a : σ → MvPowerSeries τ R} {a' : σ' → MvPowerSeries τ' R}
    (ha : ∀ i, constantCoeff (a i) = 0) (ha' : ∀ j, constantCoeff (a' j) = 0)
    (haS : ∀ i (d : τ →₀ ℕ), d.degree < g → coeff d (a i) ∈ S)
    (haS' : ∀ j (d : τ' →₀ ℕ), d.degree < g' → coeff d (a' j) ∈ S)
    {f : MvPowerSeries (σ ⊕ σ') R}
    (hf : ∀ (α : σ →₀ ℕ) (β : σ' →₀ ℕ), α.degree < g → β.degree < g' →
      coeff (α.sumElim β) f ∈ S)
    (α : τ →₀ ℕ) (β : τ' →₀ ℕ) (hα : α.degree < g) (hβ : β.degree < g') :
    coeff (α.sumElim β) (f.subst (sumFamily a a')) ∈ S := by sorry
