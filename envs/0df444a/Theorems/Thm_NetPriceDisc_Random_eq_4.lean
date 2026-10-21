-- Prove2me | Theorems.Thm_NetPriceDisc_Random_eq_4
-- name    : NetPriceDisc.Random.eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:23.903657+00:00
-- url     : https://prove2.me/theorems/c0eeba61-eee0-48cb-bd78-3d753bb615c2
-- title:
--   Eq. (4), p. 7 — p₀ = ((a+c)/2)1 is the optimal uniform price, with profit π₀ = ½((a−c)/2)² 1ᵀ(I − 2ρG/‖G+Gᵀ‖)⁻¹1
-- statement:
--   Let $a>0$, $c<a$ and $0<\rho<1$, and let $G$ be a non-empty $n\times n$ matrix with non-negative entries; write $\|G+G^{\mathsf T}\|$ for the spectral norm. Among uniform price vectors $s\mathbf 1$, $s\in\mathbb R$, the profit $\pi(s\mathbf 1)$ is maximised by $p_0=\frac{a+c}{2}\mathbf 1$, and
--   $$\pi_0=\pi(p_0)=\frac12\Big(\frac{a-c}{2}\Big)^2\,\mathbf 1^{\mathsf T}\Big(I-\frac{2\rho}{\|G+G^{\mathsf T}\|}G\Big)^{-1}\mathbf 1=\frac12\Big(\frac{a-c}{2}\Big)^2\sum_{k=0}^{\infty}\Big(\frac{2\rho}{\|G+G^{\mathsf T}\|}\Big)^k\mathbf 1^{\mathsf T}G^k\mathbf 1 .$$
--
--   So the optimal uniform price does not depend on the network, while the profit it earns is the discounted number of walks in the directed network $G$ itself. Comparing with eq. (3) gives the regret of uniform pricing.
--
--   **Formalization Note.** The three conjuncts are: $p_0$ is a greatest element of $\{\pi(s\mathbf 1):s\in\mathbb R\}$; the closed form of $\pi(p_0)$; and the series expansion of $\mathbf 1^{\mathsf T}(I-\frac{2\rho}{\|G+G^{\mathsf T}\|}G)^{-1}\mathbf 1$.
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 7, optimal uniform price p₀ and eq. (4)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem eq_4 (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) (hG0 : G ≠ 0) :
    IsGreatest (Set.range fun s : ℝ => profit a c ρ G (s • ones n))
      (profit a c ρ G (uniformPrice n a c)) ∧
    profit a c ρ G (uniformPrice n a c) =
      1 / 2 * ((a - c) / 2) ^ 2 *
        (ones n ⬝ᵥ ((1 - (2 * ρ / specNorm (G + Gᵀ)) • G)⁻¹ *ᵥ ones n)) ∧
    HasSum (fun k : ℕ => (2 * ρ / specNorm (G + Gᵀ)) ^ k * walks G k)
      (ones n ⬝ᵥ ((1 - (2 * ρ / specNorm (G + Gᵀ)) • G)⁻¹ *ᵥ ones n)) := by sorry

end NetPriceDisc.Random
