-- Prove2me | Theorems.Thm_NetPriceDisc_Random_lemma_5_2
-- name    : NetPriceDisc.Random.lemma_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:25.317+00:00
-- url     : https://prove2.me/theorems/1ac3854e-f980-4c25-9dce-cfc867764e45
-- title:
--   Lemma 5.2, p. 18 — E_G[1ᵀ(G+Gᵀ)²1] = 2n(n−1)p(1 − 3p + 2np)
-- statement:
--   Let $G$ be the directed Erdős–Rényi network $G(n,q)$ with $0\le q\le1$. The expected number of walks of length $2$ in the multigraph $G+G^{\mathsf T}$ is
--   $$\mathbb E_G\big[\mathbf 1^{\mathsf T}(G+G^{\mathsf T})^2\mathbf 1\big]=2n(n-1)q\,(1-3q+2nq).$$
--
--   Combined with (29), this bounds the expected regret in sparse networks.
--
--   **Formalization Note.** $n$ is cast to the reals, so $n-1$ is real subtraction (both sides are $0$ at $n=0$). The paper writes $p(n)$ for the density; here it is $q$.
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 18, Lemma 5.2 (proof p. 29, App. C.2)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem lemma_5_2 (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    erExpect n q (fun G => walks (G + Gᵀ) 2) =
      2 * (n : ℝ) * ((n : ℝ) - 1) * q * (1 - 3 * q + 2 * (n : ℝ) * q) := by sorry

end NetPriceDisc.Random
