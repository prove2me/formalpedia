-- Prove2me | Theorems.Thm_NetPriceDisc_Random_lemma_5_5_ii
-- name    : NetPriceDisc.Random.lemma_5_5_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:33.188516+00:00
-- url     : https://prove2.me/theorems/85e22c78-06c6-46e2-a601-58b0404dfca7
-- title:
--   Lemma 5.5 (ii) (k ≥ 1), p. 19 — the gap E_G[1ᵀ(G+Gᵀ)ᵏ1] − 2ᵏE_G[1ᵀGᵏ1] is at most (k−1)2ᵏ⁻¹P(n,k)pᵏ⁻¹ + (k−1)ᵏ2ᵏP(n,k−1)pᵏ⁻²
-- statement:
--   Let $G$ be the directed Erdős–Rényi network $G(n,q)$. Let $k$ be an integer with $1\le k<n$ and suppose $\frac1{n-k+1}\le q<1$. Then
--   $$\mathbb E_G\big[\mathbf 1^{\mathsf T}(G+G^{\mathsf T})^k\mathbf 1\big]-2^k\,\mathbb E_G\big[\mathbf 1^{\mathsf T}G^k\mathbf 1\big]\le(k-1)2^{k-1}P(n,k)\,q^{k-1}+(k-1)^k2^kP(n,k-1)\,q^{k-2},$$
--   where $P(n,k)=\frac{n!}{(n-k)!}$ is the number of ways of permuting $k$ out of $n$ objects.
--
--   This bounds the regret contribution of walks of length $k$ in dense networks; the proof of Theorem 5.1 sums it over $2\le k\le K$.
--
--   **Formalization Note.** The paper states the range $0\le k<n$; at $k=0$ the right side involves $P(n,-1)$ and is undefined, so the statement starts at $k=1$ (where both sides are $0$). $q^{k-2}$ is an integer power, so at $k=1$ it is $q^{-1}$, as printed; its coefficient $(k-1)^k$ vanishes there. $P(n,k)$ is `Nat.descFactorial n k`.
-- source:
--   Huang, Mani & Wang, The Value of Price Discrimination in Large Random Networks, SSRN 3368458 (EC '19 submission version), p. 19, Lemma 5.5 (ii) (stated for k ≥ 1; proof pp. 30–34, App. C.5)

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
open Matrix

namespace NetPriceDisc.Random

theorem lemma_5_5_ii (n k : ℕ) (q : ℝ) (hk1 : 1 ≤ k) (hkn : k < n)
    (hq0 : 1 / ((n : ℝ) - k + 1) ≤ q) (hq1 : q < 1) :
    erExpect n q (fun G => walks (G + Gᵀ) k) - 2 ^ k * erExpect n q (fun G => walks G k) ≤
      ((k : ℝ) - 1) * 2 ^ (k - 1) * (n.descFactorial k : ℝ) * q ^ (k - 1) +
        ((k : ℝ) - 1) ^ k * 2 ^ k * (n.descFactorial (k - 1) : ℝ) * q ^ ((k : ℤ) - 2) := by sorry

end NetPriceDisc.Random
