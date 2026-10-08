-- Prove2me | Theorems.Thm_OptimalRLS_Individual_eq_68
-- name    : OptimalRLS.Individual.eq_68
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:19:05.296224+00:00
-- url     : https://prove2.me/theorems/68b94393-be21-4533-8e90-ebecabfae9ea
-- title:
--   (68), p. 28 (corrected) — Σ_{n∈D_ℓ} γₙ ≥ (u^{1/(Bc+1)}/(2Bc)) ℓ^{−Bc/(Bc+1)} for ℓ ≥ (2Bc)^{Bc+1}/u
-- statement:
--   Let $\alpha, R > 0$, $1 < b < B$, $1 \le c \le 2$, and $\epsilon = (B - b)c$, so that $bc + \epsilon = Bc$. Put
--   $$u = \frac{\epsilon}{\epsilon + 1}\alpha^c R, \qquad \gamma_n = u\, n^{-(Bc + 1)} \quad (n \ge 1), \qquad \mathcal D_\ell = \{n \ge 1 : \ell\gamma_n \le 1\}.$$
--   Then for every integer $\ell \ge (2Bc)^{Bc+1}/u$,
--   $$\sum_{n \in \mathcal D_\ell} \gamma_n \ \ge\ \frac{u^{1/(Bc+1)}}{2Bc}\, \ell^{-\frac{Bc}{Bc+1}}.$$
--
--   The tail of $(\gamma_n)$ beyond the "noise level" $1/\ell$ is of order $\ell^{-Bc/(Bc+1)}$. This is the rate that appears in Theorem 3.
--
--   **Formalization Note** The printed (68) drops the factor $u$ of $\gamma_n$ when it integrates: $\int_{x_0}^\infty u t^{-(Bc+1)}dt = \frac{u}{Bc}(u\ell)^{-Bc/(Bc+1)}$ for $x_0 = (u\ell)^{1/(Bc+1)}$, not $\frac{1}{Bc}(u\ell)^{-Bc/(Bc+1)}$. The printed constant $v = u^{-Bc/(Bc+1)}/(2Bc)$ makes the inequality false when $u < 1/2$, so the statement uses the corrected constant $u^{1/(Bc+1)}/(2Bc)$ and the corrected threshold $\ell \ge (2Bc)^{Bc+1}/u$ (in place of $2Bc(2Bcu)^{Bc}$). Theorem 3 needs only that some such constant is positive.
--   - The sum over $\mathcal D_\ell$ is written as a `tsum` of $\gamma_n$ times the indicator of $\ell\gamma_n \le 1$. It is summable because $Bc + 1 > 1$.
--   - Indices start at $0$: $\gamma_n$ is `gam b c ε α R (n-1)`.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proof of Th. 3, eq. (68), p. 28 (constant and threshold corrected)

import Mathlib
import Definitions.Def_OptimalRLS_Individual_Model

namespace OptimalRLS.Individual

/-- **(68)** (p. 28), corrected. Let `B > b`, `ε = (B − b)c` (so `bc + ε = Bc`),
`u = (ε/(ε+1)) α^c R`, `γ_n = u n^{−(Bc+1)}` and `D_ℓ = {n | ℓ γ_n ≤ 1}`. For every
`ℓ ≥ (2Bc)^{Bc+1}/u`,
`∑_{n ∈ D_ℓ} γ_n ≥ (u^{1/(Bc+1)}/(2Bc)) ℓ^{−Bc/(Bc+1)}`.
The page's integral line drops the factor `u` of `γ_n`; its constant
`v = u^{−Bc/(Bc+1)}/(2Bc)` and threshold `2Bc(2Bcu)^{Bc}` are replaced by the corrected ones. -/
theorem eq_68 (α R b c B : ℝ) (hα : 0 < α) (hR : 0 < R) (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hB : b < B) (ℓ : ℕ)
    (hℓ : (2 * B * c) ^ (B * c + 1) / ((((B - b) * c) / ((B - b) * c + 1)) * α ^ c * R) ≤ ℓ) :
    (((B - b) * c) / ((B - b) * c + 1) * α ^ c * R) ^ (1 / (B * c + 1)) / (2 * B * c)
        * (ℓ : ℝ) ^ (-(B * c / (B * c + 1)))
      ≤ ∑' n : ℕ, (if (ℓ : ℝ) * gam b c ((B - b) * c) α R n ≤ 1
          then gam b c ((B - b) * c) α R n else 0) := by sorry

end OptimalRLS.Individual
