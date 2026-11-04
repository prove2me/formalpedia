-- Prove2me | Theorems.Thm_Light_Ends_keepingBut
-- name    : Light.Ends.keepingBut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:25:58.527073+00:00
-- url     : https://prove2.me/theorems/0bea48d9-d01c-4cdd-adce-c551abebc1fa
-- title:
--   Ends: keeping But
-- statement:
--   **All other locals are as before**, for a list `xs` that contains the locals that the statement
--   assigns.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Assigns.lean#L63-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Assigns.lean#L63-L66

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast


set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Ends.keepingBut {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) (xs : List ℕ) (hxs : s.assigns ⊆ xs := by simp) :
    Ends lim P d s σ T fun σ' => Q σ' ∧ ∀ y ∉ xs, σ'.loc y = σ.loc y := by sorry
