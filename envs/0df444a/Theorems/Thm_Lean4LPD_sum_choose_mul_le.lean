-- Prove2me | Theorems.Thm_Lean4LPD_sum_choose_mul_le
-- name    : Lean4LPD.sum_choose_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:50.756822+00:00
-- url     : https://prove2.me/theorems/24a46063-bbfe-4f9d-b559-8e78863baca4
-- title:
--   Lean4 LPD: sum choose mul le
-- statement:
--   **The slot count.** The sum over Trotter steps of the layer-slot binomials, the step that
--   leads to `apd:eq:total_high_weight_norm` in the proof of `apd:thm:one_step_truncation_error`:
--
--     `Σ_{d=1}^{r} C(dΓ, K) ≤ ((r+1)Γ)^{K+1} / (Γ · (K+1)!)`.
--
--   `Γ` is a positive **natural** number, because it is a layer count and `C(dΓ, K)` counts layer
--   slots (see the module docstring). The two steps — `C(n,k) ≤ n^k/k!` and `sum_pow_le` — reproduce
--   the right-hand side exactly, so nothing is thrown away.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L127-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/StepSum.lean#L127-L161

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.sum_choose_mul_le (K r G : ℕ) (hG : 1 ≤ G) :
    ∑ i ∈ range r, (((i + 1) * G).choose K : ℝ)
      ≤ (((r : ℝ) + 1) * G) ^ (K + 1) / ((G : ℝ) * (Nat.factorial (K + 1) : ℝ)) := by sorry
