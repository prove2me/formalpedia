-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerN_le_majorant
-- name    : Lean4LPD.PauliString.layerN_le_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T08:01:23.425346+00:00
-- url     : https://prove2.me/theorems/7901bd00-f1f6-48d0-b4e9-1f449e932e03
-- title:
--   Pauli String: layer N le majorant
-- statement:
--   **The first-passage majorant for truncated Pauli layers.** The abstract bound
--   `MultiLadder.le_majorant` (`apd:eq:composition_majorant`) applied to `pauliMultiLadder`: the
--   mass of `layerTraj` above every rung `m ≥ 1` is at most the majorant built from `epsJump` and
--   `entryFactor`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerLadder.lean#L368-L380
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerLadder.lean#L368-L380

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.layerN_le_majorant (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) {ko kh : ℕ}
    (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((Ls T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ Ls T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ Ls T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (T m : ℕ) (hm : 1 ≤ m) :
    layerN Ls S O ko kh m T ≤ MultiLadder.majorant
      (epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a)
      (entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) (pauliNorm O) m T := by sorry
