-- Prove2me | Theorems.Thm_NetPriceDisc_Random_lemma_5_3
-- name    : NetPriceDisc.Random.lemma_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:26.89754+00:00
-- url     : https://prove2.me/theorems/85dc6c94-d0c8-4a52-b78d-94482b839f93
-- title:
--   Lemma 5.3 (t even), p. 18 — 1ᵀ(G+Gᵀ)ᵏ1 ≤ ‖G+Gᵀ‖ᵏ⁻ᵗ 1ᵀ(G+Gᵀ)ᵗ1 for even t ≥ 2 and k ≥ t
-- statement:
--   Let $G$ be an $n\times n$ matrix with non-negative entries, $A=G+G^{\mathsf T}$, and $\|A\|$ its spectral norm. For every even positive integer $t$ and every integer $k\ge t$,
--   $$\mathbf 1^{\mathsf T}A^k\mathbf 1\le\|A\|^{k-t}\,\mathbf 1^{\mathsf T}A^t\mathbf 1 .$$
--
--   The lemma trades walks of length $k$ for walks of a fixed shorter length at the price of a power of the spectral norm; with $t=2$ it turns the regret series into the bound (29).
--
--   **Formalization Note.** The paper states the lemma for every positive integer $t$, but as printed it is false for odd $t$: for $G$ with arcs from node $1$ to nodes $2,3,4$ (so $A$ is the star $K_{1,3}$), $t=1$ and $k=2$ give $\mathbf 1^{\mathsf T}A^2\mathbf 1=12>\sqrt3\cdot6=\|A\|\,\mathbf 1^{\mathsf T}A\mathbf 1$. The paper's proof uses $A^{t/2}$, and every use of the lemma has $t=2$. The statement is therefore made for even $t=2s$, $s\ge1$.
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 18, Lemma 5.3 (restricted to even t; proof p. 29, App. C.3)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem lemma_5_3 {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (s k : ℕ) (hs : 1 ≤ s) (hk : 2 * s ≤ k) :
    walks (G + Gᵀ) k ≤ specNorm (G + Gᵀ) ^ (k - 2 * s) * walks (G + Gᵀ) (2 * s) := by sorry

end NetPriceDisc.Random
