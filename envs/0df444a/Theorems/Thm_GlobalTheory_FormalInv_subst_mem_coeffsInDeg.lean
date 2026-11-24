-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_subst_mem_coeffsInDeg
-- name    : GlobalTheory.FormalInv.subst_mem_coeffsInDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:37.159081+00:00
-- url     : https://prove2.me/theorems/af43247d-b0e6-4d1e-a7fc-4e8472e1f5dd
-- title:
--   Formal Inv: subst mem coeffs In Deg
-- statement:
--   The Formal Inv construction uses the subst mem coeffs In Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L195-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L195-L199

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

theorem GlobalTheory.FormalInv.subst_mem_coeffsInDeg [Finite σ] {S : Subring R} {g : ℕ} {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (haS : ∀ s, a s ∈ coeffsInDeg τ S g)
    {f : MvPowerSeries σ R} (hf : f ∈ coeffsInDeg σ S g) : f.subst a ∈ coeffsInDeg τ S g := by sorry
