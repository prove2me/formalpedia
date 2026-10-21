-- Prove2me | Theorems.Thm_NetPriceDisc_Random_eq_3
-- name    : NetPriceDisc.Random.eq_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:33.872594+00:00
-- url     : https://prove2.me/theorems/f8435108-02d7-4b3b-b703-27f9adf5d940
-- title:
--   Eq. (3), p. 6 — the optimal discriminating profit π* = ½((a−c)/2)² 1ᵀ(I − ρ(G+Gᵀ)/‖G+Gᵀ‖)⁻¹1, attained, and its walk series
-- statement:
--   Let $a>0$, $c<a$ and $0<\rho<1$, and let $G$ be a non-empty $n\times n$ matrix with non-negative entries. Write $A=G+G^{\mathsf T}$ and $\|A\|$ for its spectral norm. Then the monopolist's profit $\pi(p)=(p-c\mathbf 1)^{\mathsf T}x^*(p)$ attains its maximum over all price vectors $p\in\mathbb R^n$, and the maximum value is
--   $$\pi^*=\frac12\Big(\frac{a-c}{2}\Big)^2\,\mathbf 1^{\mathsf T}\Big(I-\frac{\rho}{\|A\|}A\Big)^{-1}\mathbf 1 .$$
--   Moreover the series expansion holds:
--   $$\mathbf 1^{\mathsf T}\Big(I-\frac{\rho}{\|A\|}A\Big)^{-1}\mathbf 1=\sum_{k=0}^{\infty}\Big(\frac{\rho}{\|A\|}\Big)^k\mathbf 1^{\mathsf T}A^k\mathbf 1 .$$
--
--   This is the closed form of the optimal profit under personalised pricing: it is proportional to the discounted number of walks of all lengths in $G+G^{\mathsf T}$. Every later bound on the regret starts from it.
--
--   **Formalization Note.** The maximum is stated as `IsGreatest` of the range of $\pi$ over $\mathbb R^n$, so it also shows that the supremum defining $\pi^*$ is attained. The paper attributes the optimal price (2) and this formula to Candogan, Bimpikis and Ozdaglar; here it is stated for this paper's normalised model.
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 6, eq. (3)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem eq_3 (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) (hG0 : G ≠ 0) :
    IsGreatest (Set.range (profit a c ρ G))
      (1 / 2 * ((a - c) / 2) ^ 2 *
        (ones n ⬝ᵥ ((1 - (ρ / specNorm (G + Gᵀ)) • (G + Gᵀ))⁻¹ *ᵥ ones n))) ∧
    HasSum (fun k : ℕ => (ρ / specNorm (G + Gᵀ)) ^ k * walks (G + Gᵀ) k)
      (ones n ⬝ᵥ ((1 - (ρ / specNorm (G + Gᵀ)) • (G + Gᵀ))⁻¹ *ᵥ ones n)) := by sorry

end NetPriceDisc.Random
