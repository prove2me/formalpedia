-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_jumpAct_layerJump_single_eq_zero
-- name    : Lean4LPD.PauliString.jumpAct_layerJump_single_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:05.928814+00:00
-- url     : https://prove2.me/theorems/98d41fa7-caf1-4125-8cf4-ea48fe5f5aef
-- title:
--   Pauli String: jump Act layer Jump single eq zero
-- statement:
--   If the input Pauli `q` commutes with `G`, and `G` commutes with every generator of `L`, then
--   the sine branch of `G` annihilates `layerJump L j` of the basis vector at `q`.
--   Supporting lemma for the column estimate of `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L652-L666
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L652-L666

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

theorem Lean4LPD.PauliString.jumpAct_layerJump_single_eq_zero (L : List (PauliString n × ℝ))
    (G : PauliString n) (θ : ℝ) (hG : ∀ g ∈ L, sympForm G g.1 = 0)
    (j : ℕ) (q : PauliIndex n) (hq : sympForm G (herm q) = 0) :
    jumpAct G θ (layerJump L j (WithLp.toLp 2 (Pi.single q (1 : ℂ)))) = 0 := by sorry
