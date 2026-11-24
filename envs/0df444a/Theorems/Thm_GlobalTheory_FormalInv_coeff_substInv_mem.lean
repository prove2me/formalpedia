-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_coeff_substInv_mem
-- name    : GlobalTheory.FormalInv.coeff_substInv_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:44.224789+00:00
-- url     : https://prove2.me/theorems/f7a3a3ba-c07b-4ae9-8285-5754b0858cb4
-- title:
--   Formal Inv: coeff subst Inv mem
-- statement:
--   The Formal Inv construction uses the coeff subst Inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L482-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L482-L487

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
variable [Fintype σ] [DecidableEq σ]
variable {u v : σ → MvPowerSeries σ R}

theorem GlobalTheory.FormalInv.coeff_substInv_mem (hu : ∀ i, constantCoeff (u i) = 0) {S : Subring R} {g : ℕ}
    (hB : ∀ i j, (linearPart u)⁻¹ i j ∈ S)
    (huS : ∀ i (d : σ →₀ ℕ), d.degree < g → coeff d (u i) ∈ S) (i : σ) (d : σ →₀ ℕ)
    (hd : d.degree < g) : coeff d (substInv u i) ∈ S := by sorry
