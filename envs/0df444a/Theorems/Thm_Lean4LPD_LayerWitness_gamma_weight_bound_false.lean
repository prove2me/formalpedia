-- Prove2me | Theorems.Thm_Lean4LPD_LayerWitness_gamma_weight_bound_false
-- name    : Lean4LPD.LayerWitness.gamma_weight_bound_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:10:28.676729+00:00
-- url     : https://prove2.me/theorems/9b990afc-6764-4ad8-9fe8-ddc0df51e9e7
-- title:
--   Layer Witness: gamma weight bound false
-- statement:
--   **A reachable string of weight `6 > w* k_h^Γ = 4` in a second-order step**: the exponent of
--   the light-cone bound has to count layers, not the `Γ` groups of the Hamiltonian.
--
--   With `n = 8`, `k_h = 2`, the two brickwork layers `L₁`, `L₂` (so `Γ = 2`) and `w* = 1`, the value
--   of `w* k_h^Γ` is `4`. It is exactly the largest reachable weight after `Γ` layers
--   (`gamma_layers_weight_le` and `gamma_layers_weight_four`), and it is exceeded after the layer
--   sequence of the second-order product formula of `apd:eq:suzuki`, where the reachable Pauli `P₆`,
--   supported on qubits `0,…,5` (`support_P₆`), has weight `6`. This is consistent with
--   `reachable_weight_le`, which allows weight up to `k_h^3 = 8` for the three layers used here.
--
--   The layer sequence used here is `[L₁, L₂, L₁]`, which is the second-order step `L₁ L₂ · L₂ L₁`
--   after the two adjacent `H_Γ` half-steps are merged: the *shortest* reading of a second-order
--   step, and already one layer more than `Γ`. `gamma_weight_bound_false_unmerged` repeats it for the
--   literal `2Γ = 4` layers.
--
--   This theorem is purely combinatorial: it contains no angle and no coefficient, and it does not
--   quantify over the product-formula order `p`. That `P₆` has a nonzero coefficient in the operator
--   discarded after the second-order step is `LayerCounterexample.actual_discard_exceeds_gamma_bound`
--   in `Pauli/LayerCounterexample.lean`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L568-L570
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L568-L570

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString

theorem Lean4LPD.LayerWitness.gamma_weight_bound_false :
    ∃ q ∈ reachable (layers := [L₁, L₂, L₁]) (Z 3), 4 < q.weight := by sorry
