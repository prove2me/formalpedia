-- Prove2me | Theorems.Thm_LiuPass_mildlyHoAApprox_of_condEPPRG
-- name    : LiuPass.mildlyHoAApprox_of_condEPPRG
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T22:41:18.468308+00:00
-- url     : https://prove2.me/theorems/4a16a973-af07-4adf-addb-19266ce75438
-- title:
--   Theorem 5.2: average-case hardness of $K^t$ from rate-1 condEP-PRGs
-- statement:
--   Theorem 5.2 of the paper. Assume that for every $\gamma > 1$ there is a rate-1 efficient
--   $\mu$-condEP-PRG $G : \{0,1\}^n \to \{0,1\}^{n+\gamma\log n}$ with $\mu(n) = 1/n^2$. Then for all
--   constants $d > 0$ and $\varepsilon > 0$ and every polynomial $t(n) \ge (1+\varepsilon)n$, the
--   function $K^t$ is mildly hard-on-average to $(d \log n)$-approximate: there is a positive
--   polynomial $p$ such that every PPT heuristic $H$ satisfies, for all sufficiently large $n$,
--   $$\Pr\big[x \leftarrow \{0,1\}^n : |H(x) - K^t(x)| \le d \log n\big] \;<\; 1 - \frac{1}{p(n)} .$$
--
--   This is the quantitatively delicate direction. A uniformly random $m$-bit string has
--   $K^t$-complexity at least $m - \frac{\gamma}{4}\log n$ except with probability $n^{-\gamma/4}$,
--   while every output of the generator has $K^t$-complexity below $m - \frac{\gamma}{2}\log n$,
--   because the seed plus the constant-size code of $G$ describes it within the time bound. A
--   heuristic that approximates $K^t$ well therefore distinguishes the two distributions — but only
--   because the entropy-preserving property keeps the conditioned output distribution from
--   concentrating: it guarantees that, conditioned on a $1/n$ fraction of good seeds, the output has
--   min-entropy $n - O(\log n)$, so the heuristic's failure probability on generator outputs exceeds
--   its failure probability on uniform strings by at most a polynomial factor.
-- source:
--   Yanyi Liu, Rafael Pass, On One-way Functions and Kolmogorov Complexity, arXiv:2009.11514v1 (FOCS 2020), https://arxiv.org/abs/2009.11514, p. 11, Theorem 5.2 (with Claims 1 and 2 in its proof, pp. 12-13)

import Definitions.Def_LiuPass_crypto
open Finset
open scoped Classical

namespace LiuPass

open Finset
open scoped Classical

theorem mildlyHoAApprox_of_condEPPRG (U : UMachine)
    (hG : ∀ gamma : ℕ, 1 < gamma → ∃ G : BitStr → BitStr,
      Rate1Efficient U G ∧ IsCondEPPRG U gamma (fun n => 1 / (n : ℝ) ^ 2) G)
    (d : ℕ) (hd : 0 < d) (eps : ℝ) (heps : 0 < eps) (t : ℕ → ℕ) (ht : IsPoly t)
    (htlb : ∀ n : ℕ, (1 + eps) * (n : ℝ) ≤ (t n : ℝ)) :
    MildlyHoAApprox U (fun n => d * Nat.log 2 n) (Kt U t) := by sorry
end LiuPass
