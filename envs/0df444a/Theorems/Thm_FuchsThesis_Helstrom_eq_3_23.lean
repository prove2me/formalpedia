-- Prove2me | Theorems.Thm_FuchsThesis_Helstrom_eq_3_23
-- name    : FuchsThesis.Helstrom.eq_3_23
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:20.650471+00:00
-- url     : https://prove2.me/theorems/065afa97-dae2-4d04-978d-f2bf7389fb2a
-- title:
--   Eq. (3.23) — quantum error probability $P_e(\hat\rho_0|\hat\rho_1) = \pi_0 + \sum_{\gamma_j\le0}\gamma_j$
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be density operators on a finite-dimensional Hilbert space and let $\pi_0, \pi_1 \ge 0$ with $\pi_0 + \pi_1 = 1$ be prior probabilities. Let $\gamma_j$ be the eigenvalues (with multiplicity) of the Hermitian operator $\hat\Gamma = \pi_1\hat\rho_1 - \pi_0\hat\rho_0$. Then the quantum error probability
--
--   $$
--   P_e(\hat\rho_0|\hat\rho_1) = \min_{\{\hat E_b\}} \sum_b \min\big\{\pi_0\,\mathrm{tr}(\hat\rho_0\hat E_b),\ \pi_1\,\mathrm{tr}(\hat\rho_1\hat E_b)\big\},
--   $$
--
--   minimized over all POVMs with any finite number of outcomes, has the explicit form
--
--   $$
--   P_e(\hat\rho_0|\hat\rho_1) = \pi_0 + \sum_{\gamma_j \le 0} \gamma_j ,
--   $$
--
--   and the minimum is attained by some POVM.
--
--   This is Helstrom's formula for discriminating two quantum states with arbitrary priors, derived without variational methods. For equal priors it becomes $\tfrac12 - \tfrac14\,\mathrm{tr}|\hat\rho_0 - \hat\rho_1|$.
--
--   Differences from the source:
--   - encoding: the "min" in (3.9) → `qErrorProb`, the infimum of the set of values over every POVM `E : Fin m → Matrix n n ℂ` (any $m$), plus a second conjunct asserting a POVM that attains $\pi_0 + \sum_{\gamma_j\le0}\gamma_j$; reason: together the two conjuncts say the minimum exists and equals the formula.
--   - encoding: $\sum_{\gamma_j\le0}\gamma_j$ → $\sum_j \min(\gamma_j, 0)$ over `Matrix.IsHermitian.eigenvalues` of $\hat\Gamma$, indexed with multiplicity as in (3.16); $\mathrm{tr}$ → real part of the trace; reason: same values.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.23), p.46 (PDF p.55); definition (3.9), p.44 (PDF p.53); (3.12), p.45 (PDF p.54)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsThesis_Helstrom_bayesError
import Definitions.Def_FuchsThesis_Helstrom_qErrorProb
import Definitions.Def_FuchsThesis_Helstrom_gammaOp

open scoped ComplexOrder

namespace FuchsThesis.Helstrom

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.23), p.46 (PDF p.55), with the definition (3.9), p.44 (PDF p.53):
for density operators `ρ̂₀, ρ̂₁` on a finite-dimensional space and priors `π₀, π₁ ≥ 0`,
`π₀ + π₁ = 1`, the quantum error probability is
`P_e(ρ̂₀|ρ̂₁) = π₀ + ∑_{γ_j ≤ 0} γ_j`, where `γ_j` are the eigenvalues of `Γ̂ = π₁ρ̂₁ − π₀ρ̂₀` (3.12),
and the minimum in (3.9) is attained by some POVM.

**Formalization Note.** `P_e(ρ̂₀|ρ̂₁)` is `qErrorProb`, the infimum over every POVM with any finite
number of outcomes; the source's "min" is the second conjunct (a POVM attaining the value). The
eigenvalues are `Matrix.IsHermitian.eigenvalues` of `Γ̂` (with multiplicity), and
`∑_{γ_j ≤ 0} γ_j` is written `∑ j, min γ_j 0`. -/
theorem eq_3_23 {n : Type} [Fintype n] [DecidableEq n] (π0 π1 : ℝ) (hπ0 : 0 ≤ π0)
    (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1) (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1) :
    qErrorProb π0 π1 ρ0 ρ1 =
        π0 + ∑ j, min ((gammaOp_isHermitian (π0 := π0) (π1 := π1) h0.1.isHermitian
          h1.1.isHermitian).eigenvalues j) 0 ∧
      ∃ (m : ℕ) (E : Fin m → Matrix n n ℂ), FuchsVdGraaf.IsPOVM E ∧
        bayesError π0 π1 ρ0 ρ1 E =
          π0 + ∑ j, min ((gammaOp_isHermitian (π0 := π0) (π1 := π1) h0.1.isHermitian
            h1.1.isHermitian).eigenvalues j) 0 := by sorry

end FuchsThesis.Helstrom
