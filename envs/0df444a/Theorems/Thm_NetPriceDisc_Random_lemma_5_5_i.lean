-- Prove2me | Theorems.Thm_NetPriceDisc_Random_lemma_5_5_i
-- name    : NetPriceDisc.Random.lemma_5_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:29.596562+00:00
-- url     : https://prove2.me/theorems/62de1369-915e-430d-a5d8-fd6bca75908c
-- title:
--   Lemma 5.5 (i), p. 19 — E_G[1ᵀ(G+Gᵀ)ᵏ1] ≥ 2ᵏ E_G[1ᵀGᵏ1] for every k ≥ 0
-- statement:
--   Let $G$ be the directed Erdős–Rényi network $G(n,q)$ with $0\le q\le1$. For every integer $k\ge0$,
--   $$\mathbb E_G\big[\mathbf 1^{\mathsf T}(G+G^{\mathsf T})^k\mathbf 1\big]\ge2^k\,\mathbb E_G\big[\mathbf 1^{\mathsf T}G^k\mathbf 1\big].$$
--
--   In expectation, the profit contribution of walks of length $k$ under discriminating prices dominates that under uniform pricing, so each term of the regret series has non-negative expectation.
--
--   **Formalization Note.** The inequality is stated for expectations only: it fails for individual networks (p. 19 gives a 5-node example with $\mathbf 1^{\mathsf T}(G+G^{\mathsf T})^3\mathbf 1=134<136=2^3\mathbf 1^{\mathsf T}G^3\mathbf 1$).
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 19, Lemma 5.5 (i) (proof pp. 30–34, App. C.5)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem lemma_5_5_i (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    2 ^ k * erExpect n q (fun G => walks G k) ≤ erExpect n q (fun G => walks (G + Gᵀ) k) := by sorry

end NetPriceDisc.Random
