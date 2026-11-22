-- Prove2me | Theorems.Thm_Lean4LPD_tZeroModel_le_tZero
-- name    : Lean4LPD.tZeroModel_le_tZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:51.364324+00:00
-- url     : https://prove2.me/theorems/1d2f209d-377d-4616-bb9e-1cb567d78e3a
-- title:
--   Lean4 LPD: t Zero Model le t Zero
-- statement:
--   **The model threshold is a sound under-approximation of the paper's.** Since `c₀ ≤ 2` under
--   the hypotheses `m* ≥ 1`, `r ≥ 5` and `B ≤ 1` of `Lean4LPD.cZero_le_two`, one has `t₀^model ≤ t₀`,
--   so restricting to `t < t₀^model` is conservative: it can only shrink the admissible window. This
--   is the lemma that licenses the substitution, and it is `Lean4LPD.cZero_le_two` that makes it
--   available — without a uniform bound on `c₀` there would be nothing to compare against.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Total.lean#L105-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Total.lean#L105-L122

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.tZeroModel_le_tZero {r m G B kh a : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hr5 : 5 ≤ r)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hkh : 1 < kh) (ha : 0 < a) :
    tZeroModel G kh a ≤ tZero (cZero r m G B) G kh a := by sorry
