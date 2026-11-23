-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_subst_mem_coeffsIn
-- name    : GlobalTheory.FormalInv.subst_mem_coeffsIn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:57.198204+00:00
-- url     : https://prove2.me/theorems/78577619-0612-46e4-a586-83c3e64df089
-- title:
--   Formal Inv: subst mem coeffs In
-- statement:
--   The Formal Inv construction uses the subst mem coeffs In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L174-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L174-L186

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

theorem GlobalTheory.FormalInv.subst_mem_coeffsIn {κ : Type*} {S : Subring R} {w : κ → τ → ℕ} {w' : κ → σ → ℕ}
    {g : κ → ℕ} {a : σ → MvPowerSeries τ R} (ha' : HasSubst a)
    (ha : ∀ k s, a s ∈ weightGe (w k) (w' k s)) (haS : ∀ s, a s ∈ coeffsIn S w g)
    {f : MvPowerSeries σ R} (hf : f ∈ coeffsIn S w' g) : f.subst a ∈ coeffsIn S w g := by sorry
