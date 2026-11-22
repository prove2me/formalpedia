-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauli_rotation_branch_anticommute_bounds
-- name    : Lean4LPD.PauliString.pauli_rotation_branch_anticommute_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:56.86508+00:00
-- url     : https://prove2.me/theorems/02a07138-b208-4a74-99d9-8f82ead5e057
-- title:
--   Pauli String: pauli rotation branch anticommute bounds
-- statement:
--   **The anticommuting branch with the bounds that go with it**, for a `k_h`-local generator.
--
--   The conjuncts are, in order: the identity; the two halves of the weight bound; and the
--   non-collinearity of the two terms.
--
--   Measured against the three consequences the paper draws from `apd:eq:pauli_rotation_branch`,
--   that is **consequence (2), the weight bound, in full**, the **non-degeneracy half of (3)** — the
--   `i sin(θ)` coefficient is not a rescaling of the first term — and **none of (1)**, which is a
--   statement about coefficients in the Pauli basis and needs a basis that this file does not build
--   (see the module docstring). The subtraction `weight s - (kh - 1)` is truncated subtraction in
--   `ℕ`; that is harmless, since when it truncates to `0` the lower bound holds trivially.
--
--   Stated as one theorem because the paper states one equation with one set of consequences, and
--   because a reader checking the correspondence should not have to assemble it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Branch.lean#L186-L196
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Branch.lean#L186-L196

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

theorem Lean4LPD.PauliString.pauli_rotation_branch_anticommute_bounds (hG : IsSelfAdjoint G) (h : sympForm G s = 1)
    (hk : weight G ≤ kh) (θ : ℝ) :
    rot (toMatrix G) θ * toMatrix s * rot (toMatrix G) (-θ)
        = (Real.cos θ : ℂ) • toMatrix s + (Complex.I * Real.sin θ) • toMatrix (G * s)
      ∧ weight s - (kh - 1) ≤ weight (G * s)
      ∧ weight (G * s) ≤ weight s + (kh - 1)
      ∧ ∀ c : ℂ, toMatrix (G * s) ≠ c • toMatrix s := by sorry
