-- Prove2me | Theorems.Thm_FuchsThesis_Fidelity_eq_3_67
-- name    : FuchsThesis.Fidelity.eq_3_67
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:46.46509+00:00
-- url     : https://prove2.me/theorems/24362c71-9064-4cc9-9912-45cf456f8b50
-- title:
--   Eqs. (3.64), (3.67) — for invertible states $\hat M$ is Hermitian and nonnegative
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be invertible density operators on a finite-dimensional space and put $\hat S = \sqrt{\hat\rho_1^{1/2}\hat\rho_0\hat\rho_1^{1/2}}$. Then
--
--   $$
--   \hat U_c \equiv \hat S\,\hat\rho_1^{-1/2}\hat\rho_0^{-1/2}
--   $$
--
--   is unitary and is the unique operator with $\hat U_c\hat\rho_0^{1/2}\hat\rho_1^{1/2} = \hat S$. Moreover the operator
--
--   $$
--   \hat M \equiv \hat\rho_0^{1/2}\hat U_c^\dagger\hat\rho_1^{-1/2} = \hat\rho_1^{-1/2}\hat S\,\hat\rho_1^{-1/2}
--   $$
--
--   is Hermitian and nonnegative.
--
--   The eigenbasis of $\hat M$ is the measurement that attains the fidelity in the invertible case.
--
--   **Formalization Note** Invertibility is hypothesized because the source assumes it for this passage; it is what makes the matrix inverse of $\hat\rho_k^{1/2}$ the true $\hat\rho_k^{-1/2}$.
--
--   Differences from the source:
--   - encoding: ρ̂_k^{-1/2} → `(CFC.sqrt ρ_k)⁻¹`; reason: for invertible ρ̂_k this is the inverse of the nonnegative root, the meaning of the symbol
--   - reading: Û_c "uniquely" satisfies (3.63) and is introduced as a unitary operator → the conclusion states unitarity and ∀ U, (3.63) ↔ U = Û_c; reason: spells out what (3.64) asserts about the displayed formula
--   - encoding: "Hermitian and also nonnegative" → `Matrix.PosSemidef`; reason: that predicate is exactly Hermitian and nonnegative
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eqs. (3.64) and (3.67), p.53 (PDF p.62), and p.54 (PDF p.63)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsVdGraaf_outcomeDist
import Definitions.Def_FuchsVdGraaf_bhattacharyya
import Definitions.Def_FuchsVdGraaf_qBhattacharyya
open Matrix
open scoped MatrixOrder ComplexOrder
open WildeQIT FuchsVdGraaf

namespace FuchsThesis.Fidelity

/-- Fuchs, arXiv:quant-ph/9601020v1, eqs. (3.64) and (3.67), p.53 (PDF p.62), and the claim at the
top of p.54 (PDF p.63): when `ρ̂₀` and `ρ̂₁` are both invertible, (3.63) is uniquely satisfied by
`Û_c ≡ √(ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2}) ρ̂₁^{-1/2} ρ̂₀^{-1/2}`, and
`M̂ ≡ ρ̂₀^{1/2} Û_c† ρ̂₁^{-1/2} = ρ̂₁^{-1/2} √(ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2}) ρ̂₁^{-1/2}` is Hermitian and
nonnegative.

**Formalization Note.** The invertibility the source assumes for this passage is the pair of
hypotheses `IsUnit ρ0`, `IsUnit ρ1`, which also makes `Matrix`'s total inverse `⁻¹` the true
inverse of `ρ̂_k^{1/2}`. `Matrix.PosSemidef` carries both "Hermitian" and "nonnegative". -/
theorem eq_3_67 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : IsDensityOperator ρ0) (h1 : IsDensityOperator ρ1)
    (h0inv : IsUnit ρ0) (h1inv : IsUnit ρ1)
    (Uc : Matrix n n ℂ)
    (hUc : Uc = CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1) * (CFC.sqrt ρ1)⁻¹ * (CFC.sqrt ρ0)⁻¹) :
    Uc ∈ unitaryGroup n ℂ ∧
    (∀ U : Matrix n n ℂ,
      U * CFC.sqrt ρ0 * CFC.sqrt ρ1 = CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1) ↔ U = Uc) ∧
    CFC.sqrt ρ0 * Ucᴴ * (CFC.sqrt ρ1)⁻¹ =
      (CFC.sqrt ρ1)⁻¹ * CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1) * (CFC.sqrt ρ1)⁻¹ ∧
    ((CFC.sqrt ρ1)⁻¹ * CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1) *
      (CFC.sqrt ρ1)⁻¹).PosSemidef := by sorry

end FuchsThesis.Fidelity
