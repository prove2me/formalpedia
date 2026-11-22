-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauli_rotation_branch_anticommute_hermitian
-- name    : Lean4LPD.PauliString.pauli_rotation_branch_anticommute_hermitian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:44.189798+00:00
-- url     : https://prove2.me/theorems/9c51f984-f91f-4fbd-9909-2abeb9641355
-- title:
--   Pauli String: pauli rotation branch anticommute hermitian
-- statement:
--   **The anticommuting branch in the variables of the norm-flow proof**: a *real* coefficient on
--   a *Hermitian* partner.
--
--   The proof of `apd:thm:local_flow_k_local` treats conjugation as a real orthogonal matrix acting on
--   the coefficient vector in the Pauli basis: the Paulis anticommuting with the generator are paired
--   as `s ↔ ±i G_g s`, and each pair undergoes a planar rotation by the angle `dt`.
--   `pauli_rotation_branch_anticommute` above is not yet in that form: it carries the complex
--   coefficient `i sin θ` on `G s`, and `G s` is *anti*-Hermitian when `G` and `s` anticommute.
--   Absorbing the `i` into the operator fixes both at once — `i G s` is Hermitian
--   (`isSelfAdjoint_phaseMul_one_mul`) and the coefficient becomes the real `sin θ`.
--
--   This is the form consumed by the coefficient-vector computation `coeff_conj` in
--   `Pauli/Flow.lean`, and the reason `isSelfAdjoint_phaseMul_one_mul` and
--   `weight_sub_le_weight_phaseMul_one_mul` are stated about the partner rather than the bare
--   product.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Branch.lean#L164-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Branch.lean#L164-L170

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Rotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s : PauliString n} {θ : ℝ} {kh : ℕ}

theorem Lean4LPD.PauliString.pauli_rotation_branch_anticommute_hermitian (hG : IsSelfAdjoint G)
    (h : sympForm G s = 1) (θ : ℝ) :
    rot (toMatrix G) θ * toMatrix s * rot (toMatrix G) (-θ)
      = (Real.cos θ : ℂ) • toMatrix s
        + (Real.sin θ : ℂ) • toMatrix (phaseMul 1 (G * s)) := by sorry
