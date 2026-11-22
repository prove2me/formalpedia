-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerJump_apply_eq_zero_of_weight_lt
-- name    : Lean4LPD.PauliString.layerJump_apply_eq_zero_of_weight_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:18.239631+00:00
-- url     : https://prove2.me/theorems/7ba3d099-4a5a-4284-bc76-8887f35f7328
-- title:
--   Pauli String: layer Jump apply eq zero of weight lt
-- statement:
--   **Exactly `j` sine branches raise the Pauli weight by at most `j (k_h - 1)`.**
--   If the input has no coefficient above weight `w`, then `layerJump L j` of it has none above
--   `w + j (k_h - 1)`; this is the weight bookkeeping of `apd:thm:layer_inflow`. Cancellations can
--   remove coefficients, so only support containment is asserted. No disjointness is needed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L280-L310
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L280-L310

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

theorem Lean4LPD.PauliString.layerJump_apply_eq_zero_of_weight_lt (L : List (PauliString n × ℝ))
    {kh w : ℕ} (hk : ∀ g ∈ L, weight g.1 ≤ kh)
    (y : EuclideanSpace ℂ (PauliIndex n))
    (hy : ∀ p : PauliIndex n, w < wt p → y.ofLp p = 0)
    (j : ℕ) (p : PauliIndex n) (hp : w + j * (kh - 1) < wt p) :
    (layerJump L j y).ofLp p = 0 := by sorry
