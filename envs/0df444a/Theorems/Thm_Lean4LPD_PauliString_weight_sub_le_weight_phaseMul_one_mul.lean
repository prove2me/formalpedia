-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_sub_le_weight_phaseMul_one_mul
-- name    : Lean4LPD.PauliString.weight_sub_le_weight_phaseMul_one_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:09:16.377415+00:00
-- url     : https://prove2.me/theorems/af3bc36e-f0ab-403f-9301-87711198f0f7
-- title:
--   Pauli String: weight sub le weight phase Mul one mul
-- statement:
--   The same bound for the Hermitian partner `i G s`. In the proof of
--   `apd:thm:local_flow_k_local` a high-weight Pauli `s` is connected to its partner `i G s`, not to
--   the bare product `G s`. The two have the same weight, because the weight cannot see a phase
--   (`weight_phaseMul`), so this is `weight_sub_le_weight_mul` restated for the object the proof
--   actually uses.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L355-L358
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L355-L358

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
variable {kh : ℕ}

theorem Lean4LPD.PauliString.weight_sub_le_weight_phaseMul_one_mul (hk : weight G ≤ kh) (h : sympForm G s = 1) :
    weight s - (kh - 1) ≤ weight (phaseMul 1 (G * s)) := by sorry
