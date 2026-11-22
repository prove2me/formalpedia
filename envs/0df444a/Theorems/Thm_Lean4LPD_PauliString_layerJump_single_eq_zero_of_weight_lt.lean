-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerJump_single_eq_zero_of_weight_lt
-- name    : Lean4LPD.PauliString.layerJump_single_eq_zero_of_weight_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:20.982526+00:00
-- url     : https://prove2.me/theorems/abfb0e04-6f06-4ad9-9265-fcc3c660b661
-- title:
--   Pauli String: layer Jump single eq zero of weight lt
-- statement:
--   Finite-support transfer in a `j`-branch matrix column: the input basis vector at `q` can
--   reach only coordinates of weight at most `wt q + j(k_h-1)`.
--   Supporting lemma for the row bound of `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L315-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L315-L322

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

theorem Lean4LPD.PauliString.layerJump_single_eq_zero_of_weight_lt (L : List (PauliString n × ℝ))
    {kh : ℕ} (hk : ∀ g ∈ L, weight g.1 ≤ kh) (j : ℕ) (p q : PauliIndex n)
    (hp : wt q + j * (kh - 1) < wt p) :
    (layerJump L j (WithLp.toLp 2 (Pi.single q (1 : ℂ)))).ofLp p = 0 := by sorry
