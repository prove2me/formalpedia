-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_eq_5
-- name    : MMSImpossibility.Goods.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:18:33.841894+00:00
-- url     : https://prove2.me/theorems/81aea8e0-fa9d-4d85-a5ca-cdac524819da
-- title:
--   Equation (5) — at most $2d$ $X$-goods in $B_Q$
-- statement:
--   Throughout, $n \ge 2^{16}$, $k = 8\lceil \log_2 n\rceil$, and the instance of §2.1 has $m = n+5k$ goods: $Z_j, X_j, Y_j$ ($0\le j<2k$), $G_h$ ($0\le h<k$), $P$, $Q$ and $D_t$ ($1\le t\le n-2k-2$), with auxiliary weights $w$ and, for an agent of type $S$, valuation $v_S(g) = 3w(g)+\rho_S(g)$ (equation (3)); $\mu = 3T = 204k^3$ and $\ell = k/24$.
--
--   Setting of the proof of Proposition 8: each agent $i$ has the type $S_i = S(\sigma_i)$ of a balanced word $\sigma_i \in L_k$, the words are pairwise distinct, and $(B_1,\dots,B_n)$ is an allocation in which every agent receives $v_{S_i}(B_i) \ge \mu - \ell$. Let $B_P$, $B_Q$ be the bundles containing $P$ and $Q$, and $S_P$, $S_Q$ the types of their recipients. With $I_Q = \{j\in S_Q : Y_j\in B_Q\}$ and $d = k-|I_Q|$,
--
--   $$\big|\{j : X_j\in B_Q\}\big| \le 2d. \quad (5)$$
--
--   Together with (4) it shows that most labels of $S_Q$ have their $X$-goods in $B_P$.
--
--   Differences from the source:
--   - generalization: agent types are label sets of distinct codewords chosen from the code C of Lemma 5 → any injective assignment σ of balanced words in L_k; the code's distance and size are not assumed; reason: C ⊆ L_k and the codewords are distinct, so the paper's assignment is one instance; this step of the proof uses no distance property
--   - encoding: the item set M of the instance (families Z, X, Y, G, P, Q, D_1..D_{n-2k-2}) → items Fin (n + 5k) decoded by index ranges into the families, D_t indexed from 0; reason: for n ≥ 2k + 2 the decoding is a bijection onto the paper's item set; it changes no instance
--   - encoding: an allocation (B_1, …, B_n), an ordered partition of M into possibly empty bundles → a map A : Fin (n + 5k) → Fin n with B_i = A⁻¹(i); reason: the two describe the same objects (every item allocated, bundles may be empty)
--   - encoding: B_P, B_Q the bundles containing P and Q → the bundles of agents A p and A q, where p, q are the item indices decoding to P and Q; reason: p and q are the unique such indices; same bundles
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, proof of Proposition 8, equation (5), PDF p. 11 (printed p. 10)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Instance

namespace MMSImpossibility.Goods

/-- Equation (5) (PDF p. 11), in the setting of the proof of Proposition 8 (as for
equation (4)): the number of `X`-goods in `B_Q` is at most `2d`,
`|{j : X_j ∈ B_Q}| ≤ 2d`, where `d = k - |I_Q|`. -/
theorem eq_5 (n : ℕ) (hn : 2 ^ 16 ≤ n) (σ : Fin n → (Fin (kOf n) → Fin 2))
    (hσ : ∀ i, σ i ∈ balancedWords (kOf n)) (hinj : Function.Injective σ)
    (A : Fin (n + 5 * kOf n) → Fin n)
    (hA : ∀ i, mu (kOf n) - ell (kOf n) ≤ valuation n σ i (bundle A i))
    (p q : Fin (n + 5 * kOf n)) (hp : decode n (kOf n) p = Good.P)
    (hq : decode n (kOf n) q = Good.Q) :
    (xLabels (bundle A (A q))).card
      ≤ 2 * dCount (labelSet (σ (A q))) (bundle A (A q)) := by sorry

end MMSImpossibility.Goods
