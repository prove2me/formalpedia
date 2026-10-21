-- Prove2me | Theorems.Thm_NetPriceDisc_Random_eq_29
-- name    : NetPriceDisc.Random.eq_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:35.680369+00:00
-- url     : https://prove2.me/theorems/df23c850-3c25-4d94-9b68-b481e52a7afa
-- title:
--   Eq. (29), p. 36 — E_G[R(p₀)] ≤ ½((a−c)/2)² E_G[ρ²/(1−ρ) ‖G+Gᵀ‖⁻² 1ᵀ(G+Gᵀ)²1]
-- statement:
--   Let $a>0$, $c<a$, $0<\rho<1$, and let $G$ be the directed Erdős–Rényi network $G(n,q)$ with $0\le q\le1$. Then the expected regret of uniform pricing satisfies
--   $$\mathbb E_G[R(p_0)]\le\frac12\Big(\frac{a-c}{2}\Big)^2\,\mathbb E_G\Big[\frac{\rho^2}{1-\rho}\Big(\frac{1}{\|G+G^{\mathsf T}\|}\Big)^2\mathbf 1^{\mathsf T}(G+G^{\mathsf T})^2\mathbf 1\Big].$$
--
--   This is the basic regret bound from which the proof of Theorem 5.1 starts: walks of length $0$ and $1$ contribute nothing to the regret, and longer walks are controlled by walks of length $2$.
--
--   **Formalization Note.** For the empty network the spectral norm is $0$ and Lean's $1/0=0$ makes the integrand $0$; the regret of the empty network is also $0$ (see the Model file), so both sides agree on that outcome.
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 36, Appendix D, eq. (29)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem eq_29 (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    erExpect n q (regret a c ρ) ≤
      1 / 2 * ((a - c) / 2) ^ 2 *
        erExpect n q (fun G => ρ ^ 2 / (1 - ρ) * (1 / specNorm (G + Gᵀ)) ^ 2 * walks (G + Gᵀ) 2) := by sorry

end NetPriceDisc.Random
