-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_proposition_8
-- name    : MMSImpossibility.Goods.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:18:28.343343+00:00
-- url     : https://prove2.me/theorems/dc93bd66-324d-4592-ac22-317583866bb6
-- title:
--   Proposition 8 — every allocation leaves some agent strictly below $\mu - k/24$
-- statement:
--   Throughout, $n \ge 2^{16}$, $k = 8\lceil \log_2 n\rceil$, and the instance of §2.1 has $m = n+5k$ goods: $Z_j, X_j, Y_j$ ($0\le j<2k$), $G_h$ ($0\le h<k$), $P$, $Q$ and $D_t$ ($1\le t\le n-2k-2$), with auxiliary weights $w$ and, for an agent of type $S$, valuation $v_S(g) = 3w(g)+\rho_S(g)$ (equation (3)); $\mu = 3T = 204k^3$ and $\ell = k/24$.
--
--   Let each agent $i$ have the type $S(\sigma_i)$ of a balanced word $\sigma_i \in L_k$, with $d_H(\sigma_i,\sigma_j)\ge k/4$ for distinct agents $i\ne j$ (types are distinct codewords of a code of minimum distance at least $k/4$). Then every allocation $(B_1,\dots,B_n)$ of the $n+5k$ goods gives some agent $i$
--
--   $$v_{S_i}(B_i) < \mu - \frac{k}{24}.$$
--
--   With Lemma 6 this is the core of Theorem 1.
--
--   Differences from the source:
--   - generalization: agents receive n distinct codewords of a code C satisfying the requirements of Lemma 5 (C ⊆ L_k, |C| ≥ 2^{k/8}, minimum distance ≥ k/4) → any assignment σ of balanced words with pairwise Hamming distance ≥ k/4 (written k ≤ 4·d_H); the size of a surrounding code is not assumed; reason: the image of σ is such a code; the paper's assignment is one instance
--   - encoding: the item set M of the instance (families Z, X, Y, G, P, Q, D_1..D_{n-2k-2}) → items Fin (n + 5k) decoded by index ranges into the families, D_t indexed from 0; reason: for n ≥ 2k + 2 the decoding is a bijection onto the paper's item set; it changes no instance
--   - encoding: an allocation (B_1, …, B_n), an ordered partition of M into possibly empty bundles → a map A : Fin (n + 5k) → Fin n with B_i = A⁻¹(i); reason: the two describe the same objects (every item allocated, bundles may be empty)
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, Proposition 8, PDF p. 9 (printed p. 8); proof PDF pp. 9–12

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Instance

namespace MMSImpossibility.Goods

/-- Proposition 8 (PDF p. 9): let `n ≥ 2^16`, `k = 8⌈log₂ n⌉`, and give the agents types from
a code of balanced words with minimum distance at least `k/4`: `σ i ∈ L_k` and
`d_H(σ i, σ j) ≥ k/4` for distinct agents (so the types are distinct). Then every
allocation `A` of the `n + 5k` items gives some agent value strictly below `µ - k/24`. -/
theorem proposition_8 (n : ℕ) (hn : 2 ^ 16 ≤ n) (σ : Fin n → (Fin (kOf n) → Fin 2))
    (hσ : ∀ i, σ i ∈ balancedWords (kOf n))
    (hdist : ∀ i j, i ≠ j → kOf n ≤ 4 * hammingDist (σ i) (σ j))
    (A : Fin (n + 5 * kOf n) → Fin n) :
    ∃ i, valuation n σ i (bundle A i) < mu (kOf n) - (kOf n : ℝ) / 24 := by sorry

end MMSImpossibility.Goods
