-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_sum_steps_le
-- name    : Lean4LPD.MultiLadder.sum_steps_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:05:56.480636+00:00
-- url     : https://prove2.me/theorems/d25e10b1-04cd-483d-9eda-47d8e32d82cb
-- title:
--   Multi Ladder: sum steps le
-- statement:
--   **The globally sampled abstract ladder mass over `r` blocks.**
--
--     `∑_{d=1}^{r} N_{≥m}^{(dΓ)} ≤ ‖O‖ · ∑_{k≤m} [((r+1)Γ)^{k+1} / (Γ·(k+1)!)] · chain_k^{(m)}`.
--
--   Each ingredient is a theorem already proved rather than an estimate made here:
--   `MultiLadder.le_majorant` for the per-block bound, `majorant_eq_sum_range` to make the outer sum
--   uniform (it needs no sign hypotheses at all — both vanishings are structural), and the slot
--   count `Lean4LPD.sum_choose_mul_le` for the sum over blocks. `Γ` is a positive **integer**, as
--   appropriate for a number of layers.
--
--   The sum has the same structure as the sum over Trotter steps in the proof of
--   `apd:thm:one_step_truncation_error`, but with the slot count `C(dΓ, k)` of the accumulated mass
--   where that proof has the shifted count of the per-step inflow; see `MultiLadder.sum_block_inflow_le`
--   for the latter. A separate identification is needed before interpreting this abstract mass as
--   discarded error.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Assembly.lean#L90-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Assembly.lean#L90-L127

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Assembly
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.MultiLadder
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ} {M : ℝ}

theorem Lean4LPD.MultiLadder.sum_steps_le (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m)
    (hM : 0 ≤ M) {G : ℕ} (hG : 1 ≤ G) {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    ∑ d ∈ range r, L.N m ((d + 1) * G)
      ≤ M * ∑ k ∈ range (m + 1),
          ((((r : ℝ) + 1) * G) ^ (k + 1) / ((G : ℝ) * (Nat.factorial (k + 1) : ℝ)))
            * chain eps E k m := by sorry
