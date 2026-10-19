-- Prove2me | Theorems.Thm_NetPriceDisc_Random_eq_12_rayleigh
-- name    : NetPriceDisc.Random.eq_12_rayleigh
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:52.909384+00:00
-- url     : https://prove2.me/theorems/c9bb537c-afc8-42f9-81fc-6e96ab78fc61
-- title:
--   Eq. (12), p. 17, Rayleigh step — ‖G+Gᵀ‖ ≥ 1ᵀ(G+Gᵀ)1/1ᵀ1
-- statement:
--   Let $G$ be an $n\times n$ matrix with non-negative entries and $\|G+G^{\mathsf T}\|$ the spectral norm. Then
--   $$\|G+G^{\mathsf T}\|\ge\frac{\mathbf 1^{\mathsf T}(G+G^{\mathsf T})\mathbf 1}{\mathbf 1^{\mathsf T}\mathbf 1}.$$
--   When $G$ is a $0/1$ matrix the numerator is $2|E(G+G^{\mathsf T})|$ and the denominator is $n$.
--
--   This is the deterministic lower bound on the spectral norm by the average degree, used in the proof of Theorem 5.1 (Case 2) to compare $\|G+G^{\mathsf T}\|$ with $np$.
--
--   **Formalization Note.** Only the deterministic Rayleigh-quotient inequality of (12) is stated. The almost-sure conclusion $\|G+G^{\mathsf T}\|\ge(2+o(1))np(n)$ is not part of this statement. At $n=0$ both sides are $0$.
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 17, the Rayleigh-quotient step before eq. (12)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem eq_12_rayleigh {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ i j, 0 ≤ G i j) :
    walks (G + Gᵀ) 1 / (ones n ⬝ᵥ ones n) ≤ specNorm (G + Gᵀ) := by sorry

end NetPriceDisc.Random
