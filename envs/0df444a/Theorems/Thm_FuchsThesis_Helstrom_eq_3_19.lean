-- Prove2me | Theorems.Thm_FuchsThesis_Helstrom_eq_3_19
-- name    : FuchsThesis.Helstrom.eq_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:24.597119+00:00
-- url     : https://prove2.me/theorems/f64e81a1-e0db-4381-930d-6608f5d9421b
-- title:
--   Eq. (3.19) — the operator with $\langle j|\hat E_0^o|j\rangle = 1$ for $\gamma_j<0$, $0$ for $\gamma_j>0$ attains the bound
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be density operators, $\pi_0, \pi_1 \ge 0$ with $\pi_0 + \pi_1 = 1$, and let $\hat\Gamma = \pi_1\hat\rho_1 - \pi_0\hat\rho_0 = \sum_j \gamma_j |j\rangle\langle j|$ be any spectral decomposition. Consider operators $\hat E_0^o$ whose diagonal elements in this basis are
--
--   $$
--   \langle j|\hat E_0^o|j\rangle = 1 \ \text{ when } \gamma_j < 0, \qquad \langle j|\hat E_0^o|j\rangle = 0 \ \text{ when } \gamma_j > 0 .
--   $$
--
--   1. For any values $t_j \in [0,1]$ there is an operator $\hat E_0^o$ with $0 \le \hat E_0^o \le \hat{\mathbb 1}$ having these diagonal elements, and with $\langle j|\hat E_0^o|j\rangle = t_j$ when $\gamma_j = 0$ (the source's choice "for definiteness" is $t_j = 0$).
--   2. Every operator $\hat E_0$ with $0 \le \hat E_0 \le \hat{\mathbb 1}$ having these diagonal elements (with any values when $\gamma_j = 0$) achieves the lower bound of (3.18):
--   $$
--   \mathrm{tr}(\hat\Gamma\hat E_0) = \sum_{\gamma_j \le 0} \gamma_j .
--   $$
--
--   Together with (3.15) and (3.18), this shows that the binary POVM $\{\hat E_0^o, \hat{\mathbb 1} - \hat E_0^o\}$ is optimal.
--
--   Differences from the source:
--   - reading: the paragraph of (3.19) constructs an optimal $\hat E_0^o$ "that achieves this lower bound" by specifying its diagonal elements, any value in $[0,1]$ allowed when $\gamma_j = 0$ → clause 1 (such an operator exists, for every choice of values in $[0,1]$ on $\gamma_j = 0$) and clause 2 (every $0 \le \hat E_0 \le \hat{\mathbb 1}$ with the diagonal elements (3.19) achieves the bound); reason: these are the two claims of the paragraph; the uniqueness/diagonality discussion (3.20)–(3.22) is not part of (3.19).
--   - encoding: the spectral decomposition (3.16), $\{|j\rangle\}$ and $\langle j|\hat E|j\rangle$ → a unitary matrix $U$ (columns $|j\rangle$) and real $\gamma$ with $\hat\Gamma = U\,\mathrm{diag}(\gamma)\,U^\dagger$, any such pair, and $(U^\dagger \hat E U)_{jj}$; $\sum_{\gamma_j\le0}\gamma_j$ → $\sum_j \min(\gamma_j, 0)$; reason: Lean convention, same quantities.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.19), p.46 (PDF p.55); (3.16)–(3.18), p.45 (PDF p.54)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Helstrom_gammaOp

open scoped ComplexOrder

namespace FuchsThesis.Helstrom

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.19), p.46 (PDF p.55): let `Γ̂ = ∑_j γ_j |j⟩⟨j|` (3.16) be a
spectral decomposition of `Γ̂ = π₁ρ̂₁ − π₀ρ̂₀` (3.12). An optimal `Ê₀^o`, one that achieves the lower
bound `∑′_j γ_j` of (3.18), is obtained by specifying its diagonal elements in this basis:
`⟨j|Ê₀^o|j⟩ = 1` when `γ_j < 0` and `⟨j|Ê₀^o|j⟩ = 0` when `γ_j > 0`, and any value between 0 and 1
when `γ_j = 0`. Stated in two parts:
1. for every choice of values `t_j ∈ [0,1]` there is an operator `0 ≤ Ê₀^o ≤ 1̂` with these diagonal
   elements and `⟨j|Ê₀^o|j⟩ = t_j` when `γ_j = 0` (the source's "0 for definiteness" is `t = 0`);
2. every `0 ≤ Ê₀ ≤ 1̂` satisfying (3.19) achieves `tr(Γ̂Ê₀) = ∑_{γ_j ≤ 0} γ_j`.

**Formalization Note.** The spectral decomposition (3.16) is a unitary `U` (its columns are the
orthonormal basis `{|j⟩}`) and real `γ` with `Γ̂ = U diag(γ) U†`, any such pair; the spectral theorem
gives one, and Mathlib's `eigenvectorUnitary` with `eigenvalues` is an instance. So
`⟨j|Ê|j⟩ = (U† Ê U)_{jj}`. `∑_{γ_j ≤ 0} γ_j` is `∑ j, min γ_j 0`; the trace is its real part.
`0 ≤ Ê ≤ 1̂` is `Ê` and `1 − Ê` positive semidefinite. -/
theorem eq_3_19 {n : Type} [Fintype n] [DecidableEq n] (π0 π1 : ℝ) (hπ0 : 0 ≤ π0)
    (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1) (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) (γ : n → ℝ)
    (hΓ : gammaOp π0 π1 ρ0 ρ1 = U * Matrix.diagonal (fun j => (γ j : ℂ)) * star U) :
    (∀ t : n → ℝ, (∀ j, 0 ≤ t j ∧ t j ≤ 1) →
      ∃ E0 : Matrix n n ℂ, E0.PosSemidef ∧ (1 - E0).PosSemidef ∧
        (∀ j, γ j < 0 → (star U * E0 * U) j j = 1) ∧
        (∀ j, 0 < γ j → (star U * E0 * U) j j = 0) ∧
        (∀ j, γ j = 0 → (star U * E0 * U) j j = (t j : ℂ))) ∧
    ∀ E0 : Matrix n n ℂ, E0.PosSemidef → (1 - E0).PosSemidef →
      (∀ j, γ j < 0 → (star U * E0 * U) j j = 1) →
      (∀ j, 0 < γ j → (star U * E0 * U) j j = 0) →
      (Matrix.trace (gammaOp π0 π1 ρ0 ρ1 * E0)).re = ∑ j, min (γ j) 0 := by sorry

end FuchsThesis.Helstrom
