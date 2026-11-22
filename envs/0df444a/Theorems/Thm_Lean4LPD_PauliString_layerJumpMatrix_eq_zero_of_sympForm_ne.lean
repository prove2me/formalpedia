-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerJumpMatrix_eq_zero_of_sympForm_ne
-- name    : Lean4LPD.PauliString.layerJumpMatrix_eq_zero_of_sympForm_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:52.842899+00:00
-- url     : https://prove2.me/theorems/cb95d313-ffbc-4b5f-931a-a00cafaf01ad
-- title:
--   Pauli String: layer Jump Matrix eq zero of symp Form ne
-- statement:
--   Branches through generators that commute with `G` preserve the commutation class with `G`:
--   the entry `(p, q)` of `layerJumpMatrix L j` vanishes unless `p` and `q` have the same symplectic
--   form with `G`. Supporting lemma for the column estimate of `apd:thm:layer_inflow`. This is
--   finer than support containment: it shows that an input Pauli commuting with `G` never takes the
--   sine branch of `G`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L482-L510
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L482-L510

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

theorem Lean4LPD.PauliString.layerJumpMatrix_eq_zero_of_sympForm_ne (L : List (PauliString n × ℝ))
    (G : PauliString n) (hG : ∀ g ∈ L, sympForm G g.1 = 0)
    (j : ℕ) (p q : PauliIndex n)
    (hpq : sympForm G (herm p) ≠ sympForm G (herm q)) :
    layerJumpMatrix L j p q = 0 := by sorry
