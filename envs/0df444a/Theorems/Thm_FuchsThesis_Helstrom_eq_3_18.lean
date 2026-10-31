-- Prove2me | Theorems.Thm_FuchsThesis_Helstrom_eq_3_18
-- name    : FuchsThesis.Helstrom.eq_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:16.116361+00:00
-- url     : https://prove2.me/theorems/a6f50d11-3f0a-48e8-8b11-564429134c22
-- title:
--   Eq. (3.18) — $\mathrm{tr}(\hat\Gamma\hat E_0) \ge \sum_{\gamma_j\le 0}\gamma_j$ for every $0\le\hat E_0\le\hat{\mathbb 1}$
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be density operators, $\pi_0, \pi_1 \ge 0$ with $\pi_0 + \pi_1 = 1$, and let $\gamma_j$ be the eigenvalues (with multiplicity) of the Hermitian operator $\hat\Gamma = \pi_1\hat\rho_1 - \pi_0\hat\rho_0$. For every operator $\hat E_0$ with $0 \le \hat E_0 \le \hat{\mathbb 1}$,
--
--   $$
--   \mathrm{tr}(\hat\Gamma\hat E_0) \ge {\sum_j}' \gamma_j ,
--   $$
--
--   where the prime restricts the sum to those $j$ with $\gamma_j \le 0$.
--
--   The right side does not depend on $\hat E_0$, so it is a lower bound on the error probability $\pi_0 + \mathrm{tr}(\hat\Gamma\hat E_0)$ of every binary measurement.
--
--   Differences from the source:
--   - encoding: ${\sum_j}'\gamma_j$ over $\gamma_j \le 0$ → $\sum_j \min(\gamma_j, 0)$ over `Matrix.IsHermitian.eigenvalues` of $\hat\Gamma$, indexed with multiplicity as in (3.16); reason: same value term by term.
--   - encoding: $0 \le \hat E_0 \le \hat{\mathbb 1}$ and $\mathrm{tr}$ → $\hat E_0$ and $\hat{\mathbb 1} - \hat E_0$ positive semidefinite, real part of the trace; reason: Lean convention, the trace of the product of two Hermitian operators is real.
--   - reading: "Because $\hat\Gamma$ is neither positive- nor negative-definite" → no such hypothesis; reason: it is the source's motivation, not a condition: the proof uses only $0 \le \langle j|\hat E_0|j\rangle \le 1$, and the remark does not hold for every instance (at $\pi_0 = 0$, $\hat\rho_1 = \hat{\mathbb 1}/D$ the operator $\hat\Gamma$ is positive definite).
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.18), pp.45–46 (PDF pp.54–55)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Helstrom_gammaOp

open scoped ComplexOrder

namespace FuchsThesis.Helstrom

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.18), pp.45–46 (PDF pp.54–55): let `γ_j` be the eigenvalues of
`Γ̂ = π₁ρ̂₁ − π₀ρ̂₀` (3.12). For every operator `Ê₀` with `0 ≤ Ê₀ ≤ 1̂`,
`tr(Γ̂Ê₀) ≥ ∑′_j γ_j`, the sum restricted to those `j` with `γ_j ≤ 0`.

**Formalization Note.** The eigenvalues are `Matrix.IsHermitian.eigenvalues` of `Γ̂` (indexed by
`n`, with multiplicity); `∑_{γ_j ≤ 0} γ_j` is written `∑ j, min γ_j 0`, which has the same value.
`0 ≤ Ê₀ ≤ 1̂` is `Ê₀` and `1 − Ê₀` positive semidefinite. `tr(Γ̂Ê₀)` is the real part of the trace
(it is real since `Γ̂` and `Ê₀` are Hermitian). The source's remark that `Γ̂` "is neither positive-
nor negative-definite" is commentary and not a hypothesis. -/
theorem eq_3_18 {n : Type} [Fintype n] [DecidableEq n] (π0 π1 : ℝ) (hπ0 : 0 ≤ π0)
    (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1) (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    (E0 : Matrix n n ℂ) (hE0 : E0.PosSemidef) (hE0' : (1 - E0).PosSemidef) :
    ∑ j, min ((gammaOp_isHermitian (π0 := π0) (π1 := π1) h0.1.isHermitian
        h1.1.isHermitian).eigenvalues j) 0 ≤
      (Matrix.trace (gammaOp π0 π1 ρ0 ρ1 * E0)).re := by sorry

end FuchsThesis.Helstrom
