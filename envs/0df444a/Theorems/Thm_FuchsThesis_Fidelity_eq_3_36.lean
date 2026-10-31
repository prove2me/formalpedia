-- Prove2me | Theorems.Thm_FuchsThesis_Fidelity_eq_3_36
-- name    : FuchsThesis.Fidelity.eq_3_36
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:44.611881+00:00
-- url     : https://prove2.me/theorems/6ce53ae5-39b3-4356-933b-a1b3086b22ad
-- title:
--   Eq. (3.36) — the fidelity formula reduces to $|\langle\psi_0|\psi_1\rangle|$ on pure states
-- statement:
--   Let $|\psi_0\rangle, |\psi_1\rangle$ be unit vectors in $\mathbb C^D$ and put $\hat\rho_0 = |\psi_0\rangle\langle\psi_0|$, $\hat\rho_1 = |\psi_1\rangle\langle\psi_1|$. Then the expression $\mathrm{tr}\sqrt{\hat\rho_1^{1/2}\hat\rho_0\hat\rho_1^{1/2}}$ of Eq. (3.28) reduces as follows:
--
--   $$
--   \mathrm{tr}\sqrt{\hat\rho_1^{1/2}\hat\rho_0\hat\rho_1^{1/2}}
--   = \mathrm{tr}\sqrt{|\psi_1\rangle\langle\psi_1|\psi_0\rangle\langle\psi_0|\psi_1\rangle\langle\psi_1|}
--   = |\langle\psi_0|\psi_1\rangle|\;\mathrm{tr}\sqrt{|\psi_1\rangle\langle\psi_1|}
--   = |\langle\psi_0|\psi_1\rangle| .
--   $$
--
--   This agrees with Wootters' optimal statistical overlap for pure states and is the first evidence that (3.28) solves the optimization (3.27).
--
--   **Formalization Note** A ket is a vector $\psi : n \to \mathbb C$ with $\psi^\dagger\psi = 1$, and $|\psi\rangle\langle\psi|$ is `Matrix.vecMulVec ψ (star ψ)`. The statement is the three-link chain of the display.
--
--   Differences from the source:
--   - reading: F(ρ̂₀, ρ̂₁) on the left of (3.36) → the right side of (3.28), not the minimum (3.27); reason: the sentence before the display says the expression in Eq. (3.28) reduces
--   - encoding: unit kets |ψ⟩ and |ψ⟩⟨ψ| → `ψ : n → ℂ` with `star ψ ⬝ᵥ ψ = 1`, `vecMulVec ψ (star ψ)`; reason: the standard matrix form of the same objects
--   - encoding: tr of an operator that is nonnegative (or a real probability) → real part `.re` of the complex matrix trace; reason: the trace is real here; `.re` only moves the value from ℂ to ℝ
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.36), p.50 (PDF p.59)

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

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.36), p.50 (PDF p.59): for pure states `ρ̂₀ = |ψ₀⟩⟨ψ₀|`,
`ρ̂₁ = |ψ₁⟩⟨ψ₁|` the expression of eq. (3.28) reduces, line by line, to
`tr √(|ψ₁⟩⟨ψ₁|ψ₀⟩⟨ψ₀|ψ₁⟩⟨ψ₁|) = |⟨ψ₀|ψ₁⟩| tr √(|ψ₁⟩⟨ψ₁|) = |⟨ψ₀|ψ₁⟩|`.

**Formalization Note.** `F` in (3.36) is the right side of (3.28), not the minimum (3.27). Kets are
vectors `ψ : n → ℂ` with `⟨ψ|ψ⟩ = star ψ ⬝ᵥ ψ = 1`, and `|ψ⟩⟨ψ|` is
`Matrix.vecMulVec ψ (star ψ)`. The first conjunct is the passage from `ρ̂₁^{1/2}` in (3.28) to
`ρ̂₁ = |ψ₁⟩⟨ψ₁|` on the first line of (3.36). Traces are real and `.re` extracts the value. -/
theorem eq_3_36 {n : Type} [Fintype n] [DecidableEq n] (ψ0 ψ1 : n → ℂ)
    (hψ0 : star ψ0 ⬝ᵥ ψ0 = 1) (hψ1 : star ψ1 ⬝ᵥ ψ1 = 1) :
    (Matrix.trace (CFC.sqrt (CFC.sqrt (vecMulVec ψ1 (star ψ1)) * vecMulVec ψ0 (star ψ0) *
        CFC.sqrt (vecMulVec ψ1 (star ψ1))))).re =
      (Matrix.trace (CFC.sqrt (vecMulVec ψ1 (star ψ1) * vecMulVec ψ0 (star ψ0) *
        vecMulVec ψ1 (star ψ1)))).re ∧
    (Matrix.trace (CFC.sqrt (vecMulVec ψ1 (star ψ1) * vecMulVec ψ0 (star ψ0) *
        vecMulVec ψ1 (star ψ1)))).re =
      ‖star ψ0 ⬝ᵥ ψ1‖ * (Matrix.trace (CFC.sqrt (vecMulVec ψ1 (star ψ1)))).re ∧
    ‖star ψ0 ⬝ᵥ ψ1‖ * (Matrix.trace (CFC.sqrt (vecMulVec ψ1 (star ψ1)))).re =
      ‖star ψ0 ⬝ᵥ ψ1‖ := by sorry

end FuchsThesis.Fidelity
