-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_label_sets
-- name    : MMSImpossibility.Goods.label_sets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:17:39.620206+00:00
-- url     : https://prove2.me/theorems/a5e22437-d917-4815-a5ca-8bfe0fc8fed5
-- title:
--   Equations (1)–(2) — size, label sum and one-sided distance of label sets
-- statement:
--   Throughout, $n \ge 2^{16}$, $k = 8\lceil \log_2 n\rceil$, and the instance of §2.1 has $m = n+5k$ goods: $Z_j, X_j, Y_j$ ($0\le j<2k$), $G_h$ ($0\le h<k$), $P$, $Q$ and $D_t$ ($1\le t\le n-2k-2$), with auxiliary weights $w$ and, for an agent of type $S$, valuation $v_S(g) = 3w(g)+\rho_S(g)$ (equation (3)); $\mu = 3T = 204k^3$ and $\ell = k/24$.
--
--   For every balanced word $a \in L_k$, the label set $S(a)$ has $|S(a)| = k$ and
--
--   $$\sum_{j\in S(a)} j = k(k-1) + \frac k2. \quad (1)$$
--
--   For every two words $a, b$, $|S(a)\setminus S(b)| = d_H(a,b)$; and if $C \subseteq L_k$ has minimum distance at least $k/4$, then for distinct $a, b\in C$
--
--   $$|S(a)\setminus S(b)| = d_H(a,b) \ge \frac k4. \quad (2)$$
--
--   Equation (1) makes $\sum_{j\in S} x_j$ the same for every type; equation (2) is the distance property that Proposition 8 contradicts.
--
--   Differences from the source:
--   - generalization: label sets of the codewords a, b of the chosen code C → size and sum (1) for every balanced word; the identity |S(a) \ S(b)| = d_H(a,b) for every two words; the bound ≥ k/4 for distinct words of every code C ⊆ L_k with minimum distance ≥ k/4; reason: C ⊆ L_k, so the paper's statement is the specialization to the chosen code
--   - encoding: labels in {0, …, 2k−1}; sum k(k−1) + k/2 in the integers → labels in Fin (2k), sum of their values in ℕ with k − 1 and k/2 in ℕ; reason: k = 8⌈log₂ n⌉ ≥ 128 is even and positive, so the natural-number subtraction and division are exact
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, §2.1, equations (1) and (2), PDF p. 7 (printed p. 6)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Instance

namespace MMSImpossibility.Goods

/-- §2.1, equations (1) and (2) (PDF p. 7), for `n ≥ 2^16` and `k = 8⌈log₂ n⌉`:
label sets of balanced words have size `k` and label sum `k(k-1) + k/2`; for any two words
`|S(a) \ S(b)| = d_H(a, b)`; and for two distinct codewords of a code `C ⊆ L_k` of minimum
distance at least `k/4`, `|S(a) \ S(b)| ≥ k/4`. -/
theorem label_sets (n : ℕ) (hn : 2 ^ 16 ≤ n) :
    (∀ a ∈ balancedWords (kOf n),
      (labelSet a).card = kOf n ∧
      ∑ j ∈ labelSet a, (j : ℕ) = kOf n * (kOf n - 1) + kOf n / 2) ∧
    (∀ a b : Fin (kOf n) → Fin 2, (labelSet a \ labelSet b).card = hammingDist a b) ∧
    (∀ C : Finset (Fin (kOf n) → Fin 2), C ⊆ balancedWords (kOf n) →
      (∀ a ∈ C, ∀ b ∈ C, a ≠ b → kOf n ≤ 4 * hammingDist a b) →
      ∀ a ∈ C, ∀ b ∈ C, a ≠ b → ((kOf n : ℝ) / 4 ≤ ((labelSet a \ labelSet b).card : ℝ))) := by sorry

end MMSImpossibility.Goods
