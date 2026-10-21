-- Prove2me | Theorems.Thm_NetPriceDisc_Random_eq_9
-- name    : NetPriceDisc.Random.eq_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:07.223138+00:00
-- url     : https://prove2.me/theorems/a48c9102-5124-423c-ae5c-cfa932ed6e23
-- title:
--   Eq. (9), p. 14 — 0 < 1ᵀ((G+Gᵀ)/‖G+Gᵀ‖)ᵏ1 ≤ n for non-empty G and k > 0
-- statement:
--   Let $G$ be a non-empty $n\times n$ matrix with non-negative entries and $\|G+G^{\mathsf T}\|$ its spectral norm. For every integer $k>0$,
--   $$0<\mathbf 1^{\mathsf T}\Big(\frac{G+G^{\mathsf T}}{\|G+G^{\mathsf T}\|}\Big)^k\mathbf 1\le n .$$
--
--   The normalised walk counts are bounded by the network size, which makes every term of the profit series at most $n\rho^k$ and gives the upper bound in (14).
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 14, eq. (9)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem eq_9 {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) (hG0 : G ≠ 0)
    (k : ℕ) (hk : 0 < k) :
    0 < walks ((1 / specNorm (G + Gᵀ)) • (G + Gᵀ)) k ∧
      walks ((1 / specNorm (G + Gᵀ)) • (G + Gᵀ)) k ≤ n := by sorry

end NetPriceDisc.Random
