-- Prove2me | Theorems.Thm_KWSpectrum_Estimator_eq_21
-- name    : KWSpectrum.Estimator.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:21.588715+00:00
-- url     : https://prove2.me/theorems/7b32c666-6a70-41f0-8e3d-cba25eed8859
-- title:
--   Eq. (21) — $r^Y \le \chi_Y(\rho) \le \dim(\mathcal R_Y)\, r^Y$ for $\rho = U\operatorname{diag}(r)U^*$, $r$ decreasing
-- statement:
--   Let $Y$ be a Young frame with $N$ boxes and at most $d$ rows, $U$ a unitary $d\times d$ matrix, and $r \in \mathbb R^d$ with $r_1 \ge r_2 \ge \dots \ge r_d \ge 0$. Put $\rho = U\operatorname{diag}(r)U^*$ and $r^Y = \prod_i r_i^{Y_i}$ (with $0^0 = 1$). Then the character $\chi_Y(\rho) = \operatorname{tr}\pi_Y(\rho)$ is real and
--   $$r^Y \le \chi_Y(\rho) \le \dim(\mathcal R_Y)\; r^Y.$$
--   For $r_\alpha = e^{h_\alpha}$ this is the paper's $\exp(Y\cdot h) \le \chi_Y(\rho) \le \dim(\mathcal R_Y)\exp(Y\cdot h)$.
--
--   Combined with the polynomial bound on $\dim\mathcal R_Y$, this pins $\chi_Y(\rho)$ to $r^Y$ up to a factor polynomial in $N$, which is what makes $Y/N$ concentrate at $r$.
--
--   **Formalization Note** $\mathcal R_Y$ is the published `schurModule Y` and $\pi_Y(\rho)$ its `polynomialRepresentation`. The real part of the complex trace is compared; the imaginary part is stated to vanish.
--
--   Differences from the source:
--   - generalization: $\rho = \rho_h$ with $h \rhd 0$ (positive, strictly decreasing eigenvalues summing to one) → every $U\operatorname{diag}(r)U^*$ with $U$ unitary and $r$ weakly decreasing and nonnegative; reason: the bound holds there with $0^0 = 1$; the paper's case is $r = e^h$.
-- source:
--   Keyl & Werner, Estimating the spectrum of a density operator, arXiv:quant-ph/0102027v1, p. 4, eq. (21)

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, p. 4, eq. (21): for `ρ = U diag(r) U*` with `U`
unitary and `r₁ ≥ ⋯ ≥ r_d ≥ 0`, the character `χ_Y(ρ) = tr π_Y(ρ)` is real and
`r^Y ≤ χ_Y(ρ) ≤ dim(R_Y) r^Y`, where `r^Y = Π_i r_i^{Y_i}` (`= exp(Y · h)` for `r = exp(h)`). -/
theorem eq_21 {d N : ℕ} (Y : Partition d N) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) (hanti : Antitone r)
    (hnn : ∀ j, 0 ≤ r j) :
    let χ : ℂ := LinearMap.trace ℂ (schurModule Y)
      (polynomialRepresentation Y (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U))
    χ.im = 0 ∧
    ∏ i : Fin d, r i ^ Y.val.rowLen i.val ≤ χ.re ∧
    χ.re ≤ (Module.finrank ℂ (schurModule Y) : ℝ) * ∏ i : Fin d, r i ^ Y.val.rowLen i.val := by sorry

end KWSpectrum.Estimator
