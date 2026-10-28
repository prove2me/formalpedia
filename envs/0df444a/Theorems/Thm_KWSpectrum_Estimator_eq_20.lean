-- Prove2me | Theorems.Thm_KWSpectrum_Estimator_eq_20
-- name    : KWSpectrum.Estimator.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:55.360687+00:00
-- url     : https://prove2.me/theorems/d3f1d5f2-5096-44ef-bad1-c435a6daceb8
-- title:
--   Eq. (20) and unitary invariance — $\chi_Y(U\operatorname{diag}(r)U^*) = \sum_\mu m(\mu)\, r^\mu = s_Y(r)$
-- statement:
--   Let $Y$ be a Young frame with $N$ boxes and at most $d$ rows and $\chi_Y(\rho) = \operatorname{tr}\pi_Y(\rho)$ the character of the representation on the Schur module $\mathcal R_Y$. For every unitary $U$ and every $r \in \mathbb R^d$,
--   $$\chi_Y\big(U\operatorname{diag}(r_1,\dots,r_d)U^*\big) = \sum_{T} r^{\mu(T)} = \sum_\mu m(\mu)\, r^\mu = s_Y(r_1,\dots,r_d),$$
--   where $T$ runs over the semistandard fillings of $Y$ with entries in $\{1,\dots,d\}$ (weakly increasing along rows, strictly increasing down columns), $\mu(T)$ is the content of $T$, $r^\mu = \prod_i r_i^{\mu_i}$, and $m(\mu)$ is the number of semistandard fillings of content $\mu$. With $r_\alpha = e^{h_\alpha}$ this is the paper's $\chi_Y(\rho_h) = \sum_\mu m(\mu)\exp(\mu\cdot h)$.
--
--   The statement contains the unitary invariance $\chi_Y(U\rho U^*) = \chi_Y(\rho)$ that lets the paper assume $\rho$ diagonal, and the expansion of the character over the weights of $\pi_Y$.
--
--   **Formalization Note** $s_Y$ is the published `schurPolynomial Y`, the sum over semistandard fillings with entries in `Fin d` of the monomials of their contents; grouping fillings by content gives the weight multiplicities.
--
--   Differences from the source:
--   - generalization: $\rho = \rho_h$ with $h \rhd 0$, $\sum_j e^{h_j} = 1$ (positive, strictly decreasing eigenvalues summing to one) → $U\operatorname{diag}(r)U^*$ for every unitary $U$ and every $r \in \mathbb R^d$; reason: the identity is polynomial in $r$; the paper's case is $r = e^{h}$.
--   - reading: the multiplicity $m(\mu)$ of the weight $\mu$ (dimension of the eigenspace of $\pi_Y(\rho_h)$ with eigenvalue $e^{\mu\cdot h}$) → the number of semistandard fillings of $Y$ with content $\mu$; reason: the weight expansion is stated in its standard combinatorial form through the published Schur polynomial.
-- source:
--   Keyl & Werner, Estimating the spectrum of a density operator, arXiv:quant-ph/0102027v1, p. 3, unitary invariance before eq. (19), and eq. (20)

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, p. 3, eq. (20) with unitary invariance: for every
unitary `U` and every `r ∈ ℝ^d`, `χ_Y(U diag(r) U*) = χ_Y(diag(r)) = Σ_μ m(μ) r^μ`, the Schur
polynomial `s_Y(r)` (sum over the semistandard fillings of `Y` with entries in
`{0, …, d − 1}` of the monomial `r^{content}`). -/
theorem eq_20 {d N : ℕ} (Y : Partition d N) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) :
    LinearMap.trace ℂ (schurModule Y)
        (polynomialRepresentation Y (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U)) =
      ((MvPolynomial.eval r (schurPolynomial Y) : ℝ) : ℂ) := by sorry

end KWSpectrum.Estimator
