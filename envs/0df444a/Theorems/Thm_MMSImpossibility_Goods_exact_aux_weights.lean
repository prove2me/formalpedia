-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_exact_aux_weights
-- name    : MMSImpossibility.Goods.exact_aux_weights
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:18:12.633137+00:00
-- url     : https://prove2.me/theorems/ba0c48bf-35e4-4c58-b5b0-0817557b2b81
-- title:
--   Proof of Proposition 8, "Exact auxiliary weights" — one high good per bundle, weight exactly $T$
-- statement:
--   Throughout, $n \ge 2^{16}$, $k = 8\lceil \log_2 n\rceil$, and the instance of §2.1 has $m = n+5k$ goods: $Z_j, X_j, Y_j$ ($0\le j<2k$), $G_h$ ($0\le h<k$), $P$, $Q$ and $D_t$ ($1\le t\le n-2k-2$), with auxiliary weights $w$ and, for an agent of type $S$, valuation $v_S(g) = 3w(g)+\rho_S(g)$ (equation (3)); $\mu = 3T = 204k^3$ and $\ell = k/24$.
--
--   Setting of the proof of Proposition 8: each agent $i$ has the type $S_i = S(\sigma_i)$ of a balanced word $\sigma_i \in L_k$, the words are pairwise distinct, and $(B_1,\dots,B_n)$ is an allocation in which every agent receives $v_{S_i}(B_i) \ge \mu - \ell$. Let $B_P$, $B_Q$ be the bundles containing $P$ and $Q$, and $S_P$, $S_Q$ the types of their recipients. Then:
--
--   1. every bundle contains exactly one high good ($Z_j$, $P$, $Q$ or $D_t$);
--   2. every bundle's correction for its recipient is at most $k+1$;
--   3. every bundle has auxiliary weight exactly $T$;
--   4. every $D_t$ is alone in its bundle;
--   5. every bundle's correction for its recipient is at least $-\ell$.
--
--   This fixes the shape of any allocation that is close to MMS for everyone.
--
--   Differences from the source:
--   - generalization: agent types are label sets of distinct codewords chosen from the code C of Lemma 5 → any injective assignment σ of balanced words in L_k; the code's distance and size are not assumed; reason: C ⊆ L_k and the codewords are distinct, so the paper's assignment is one instance; this step of the proof uses no distance property
--   - encoding: the item set M of the instance (families Z, X, Y, G, P, Q, D_1..D_{n-2k-2}) → items Fin (n + 5k) decoded by index ranges into the families, D_t indexed from 0; reason: for n ≥ 2k + 2 the decoding is a bijection onto the paper's item set; it changes no instance
--   - encoding: an allocation (B_1, …, B_n), an ordered partition of M into possibly empty bundles → a map A : Fin (n + 5k) → Fin n with B_i = A⁻¹(i); reason: the two describe the same objects (every item allocated, bundles may be empty)
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, proof of Proposition 8, paragraph "Exact auxiliary weights", PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Instance

namespace MMSImpossibility.Goods

/-- Proof of Proposition 8, "Exact auxiliary weights" (PDF p. 9). Let `n ≥ 2^16`,
`k = 8⌈log₂ n⌉`, let `σ` assign distinct balanced words to the agents, and let `A` be an
allocation in which every agent `i` receives `v_{S_i}(B_i) ≥ µ - ℓ`, `ℓ = k/24`. Then every
bundle contains exactly one high good, its correction is at most `k + 1` and at least `-ℓ`,
its auxiliary weight is exactly `T`, and every `D_t` is alone in its bundle. -/
theorem exact_aux_weights (n : ℕ) (hn : 2 ^ 16 ≤ n) (σ : Fin n → (Fin (kOf n) → Fin 2))
    (hσ : ∀ i, σ i ∈ balancedWords (kOf n)) (hinj : Function.Injective σ)
    (A : Fin (n + 5 * kOf n) → Fin n)
    (hA : ∀ i, mu (kOf n) - ell (kOf n) ≤ valuation n σ i (bundle A i)) :
    (∀ i, highCount (bundle A i) = 1 ∧
      corrB (labelSet (σ i)) (bundle A i) ≤ (kOf n : ℝ) + 1 ∧
      weightB (bundle A i) = Tw (kOf n) ∧
      -ell (kOf n) ≤ corrB (labelSet (σ i)) (bundle A i)) ∧
    (∀ g : Fin (n + 5 * kOf n), (∃ t, decode n (kOf n) g = Good.D t) →
      bundle A (A g) = {g}) := by sorry

end MMSImpossibility.Goods
