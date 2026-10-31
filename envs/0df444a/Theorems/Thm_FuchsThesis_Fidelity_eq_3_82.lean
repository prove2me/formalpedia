-- Prove2me | Theorems.Thm_FuchsThesis_Fidelity_eq_3_82
-- name    : FuchsThesis.Fidelity.eq_3_82
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:59.763062+00:00
-- url     : https://prove2.me/theorems/27da34d9-886f-4bea-9f6a-fc504fb3b0be
-- title:
--   Eqs. (3.80)–(3.82) — same spectrum, and the fidelity is symmetric
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be density operators on a finite-dimensional space. The operators $\hat\rho_1^{1/2}\hat\rho_0\hat\rho_1^{1/2}$ and $\hat\rho_0^{1/2}\hat\rho_1\hat\rho_0^{1/2}$ have the same eigenvalue spectrum. Hence
--
--   $$
--   \mathrm{tr}\sqrt{\hat\rho_1^{1/2}\hat\rho_0\hat\rho_1^{1/2}} \;=\; \mathrm{tr}\sqrt{\hat\rho_0^{1/2}\hat\rho_1\hat\rho_0^{1/2}} ,
--   $$
--
--   and the quantum fidelity is symmetric: $F(\hat\rho_0,\hat\rho_1) = F(\hat\rho_1,\hat\rho_0)$.
--
--   The formula (3.28) is not visibly symmetric in its arguments, while the definition (3.27) is; this statement reconciles the two directly.
--
--   **Formalization Note** Equality of spectra with multiplicity is stated as equality of characteristic polynomials.
--
--   Differences from the source:
--   - encoding: "the same eigenvalue spectrum" → equal `Matrix.charpoly`; reason: equal characteristic polynomials are equal eigenvalue multisets
--   - reading: the intermediate value ∑_b √λ_b in (3.82) → the equality of the two outer traces, with the spectra stated separately; reason: ∑_b √λ_b is the common value that follows from equal spectra; the display asserts the equality of the outer terms
--   - encoding: F(ρ̂₀, ρ̂₁) in (3.80), the optimum (3.27) → `FuchsVdGraaf.qBhattacharyya`; reason: the published definition of the same POVM optimum, see the goal theorem
--   - encoding: tr of an operator that is nonnegative (or a real probability) → real part `.re` of the complex matrix trace; reason: the trace is real here; `.re` only moves the value from ℂ to ℝ
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eqs. (3.80)–(3.82), p.55 (PDF p.64)

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

/-- Fuchs, arXiv:quant-ph/9601020v1, eqs. (3.80)–(3.82), p.55 (PDF p.64): `ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2}` and
`ρ̂₀^{1/2} ρ̂₁ ρ̂₀^{1/2}` have the same eigenvalue spectrum, hence
`tr √(ρ̂₁^{1/2} ρ̂₀ ρ̂₁^{1/2}) = tr √(ρ̂₀^{1/2} ρ̂₁ ρ̂₀^{1/2})`, and `F(ρ̂₀, ρ̂₁) = F(ρ̂₁, ρ̂₀)`.

**Formalization Note.** "Same eigenvalue spectrum", with multiplicities, is equality of
characteristic polynomials. `F` in (3.80) is the POVM optimum (3.27), `FuchsVdGraaf.qBhattacharyya`.
Traces are real here and `.re` extracts the value. -/
theorem eq_3_82 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : IsDensityOperator ρ0) (h1 : IsDensityOperator ρ1) :
    (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1).charpoly = (CFC.sqrt ρ0 * ρ1 * CFC.sqrt ρ0).charpoly ∧
    (Matrix.trace (CFC.sqrt (CFC.sqrt ρ1 * ρ0 * CFC.sqrt ρ1))).re =
      (Matrix.trace (CFC.sqrt (CFC.sqrt ρ0 * ρ1 * CFC.sqrt ρ0))).re ∧
    qBhattacharyya ρ0 ρ1 = qBhattacharyya ρ1 ρ0 := by sorry

end FuchsThesis.Fidelity
