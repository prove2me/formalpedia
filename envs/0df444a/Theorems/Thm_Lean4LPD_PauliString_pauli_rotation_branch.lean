-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauli_rotation_branch
-- name    : Lean4LPD.PauliString.pauli_rotation_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:18.102982+00:00
-- url     : https://prove2.me/theorems/8f036e24-b8a6-46a8-90e3-82c5c4eaf74e
-- title:
--   Pauli String: pauli rotation branch
-- statement:
--   **`apd:eq:pauli_rotation_branch`, for Pauli strings, with the case split
--   closed.**
--
--     `e^{i G dt/2} s e^{-i G dt/2} = s`                                    if `⟪G,s⟫ = 0`,
--     `e^{i G dt/2} s e^{-i G dt/2} = cos(dt) s + i sin(dt) · G s`          if `⟪G,s⟫ = 1`.
--
--   The paper states the rule as two cases, `[G,P] = 0` and `{G,P} = 0`. Here the branch is
--   selected by `sympForm G s`, which takes only the values `0` and `1`
--   (`sympForm_eq_zero_or_one`) — so the `if` is total and the two branches really are all of them.
--   That is the difference between this statement and `Lean4LPD.rot_conj_of_commute` /
--   `rot_conj_of_anticommute`, which are conditioned on hypotheses that over an abstract algebra are
--   not exhaustive. That the branch *condition* is the paper's condition, and not merely a sufficient
--   one, is `toMatrix_commute_iff` and `toMatrix_anticommute_iff` — iffs at the level of operators, so
--   `sympForm G s = 0` holds exactly when `[G,P] = 0` does.
--
--   The left-hand side is written with `rot`, the closed form. By `rot_toMatrix_eq_exp` and
--   `rot_toMatrix_neg_eq_exp` in `RotationExp.lean` the two factors are the matrix exponentials
--   `exp(i G θ/2)` and `exp(-i G θ/2)`, so this is the paper's equation and not only a closed-form
--   analogue of it.
--
--   The only hypothesis is `IsSelfAdjoint G`, which by `isSelfAdjoint_iff_mul_self_eq_one` also
--   supplies the `G * G = 1` that both `rot_*` lemmas need. Note `θ` is the paper's **conjugation
--   angle** `dt`, following `Rotation.lean`'s convention: a physical rotation `e^{-i α_l G_l τ}` has
--   `dt = 2 α_l τ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Branch.lean#L125-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Branch.lean#L125-L134

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

theorem Lean4LPD.PauliString.pauli_rotation_branch (hG : IsSelfAdjoint G) (s : PauliString n) (θ : ℝ) :
    rot (toMatrix G) θ * toMatrix s * rot (toMatrix G) (-θ)
      = if sympForm G s = 0 then toMatrix s
        else (Real.cos θ : ℂ) • toMatrix s + (Complex.I * Real.sin θ) • toMatrix (G * s) := by sorry
