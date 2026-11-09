-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_construction_facts
-- name    : MMSImpossibility.Goods.construction_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:18:04.433967+00:00
-- url     : https://prove2.me/theorems/303b45b0-fc93-4cb1-92b1-5abb32c3ee8a
-- title:
--   §2.1 — construction facts: $\sum_{j\in S} x_j = U$, positive integral weights, totals $nT$ and $0$, $\mu = 204k^3$
-- statement:
--   Throughout, $n \ge 2^{16}$, $k = 8\lceil \log_2 n\rceil$, and the instance of §2.1 has $m = n+5k$ goods: $Z_j, X_j, Y_j$ ($0\le j<2k$), $G_h$ ($0\le h<k$), $P$, $Q$ and $D_t$ ($1\le t\le n-2k-2$), with auxiliary weights $w$ and, for an agent of type $S$, valuation $v_S(g) = 3w(g)+\rho_S(g)$ (equation (3)); $\mu = 3T = 204k^3$ and $\ell = k/24$.
--
--   For every type $S = S(a)$ of a balanced word $a\in L_k$:
--
--   1. $\sum_{j\in S} x_j = U$;
--   2. $n \ge 2k+2$, so the goods $D_t$ are well defined;
--   3. every auxiliary weight $w(g)$ is strictly positive and a multiple of $k$;
--   4. the total auxiliary weight is $w(M) = nT$;
--   5. the correction summed over all goods is $\rho_S(M) = 0$;
--   6. every item value $v_S(g)$ is a strictly positive integer;
--   7. the proportional share is $v_S(M)/n = \mu = 3T$, and $\mu = 204k^3$.
--
--   These are the bookkeeping facts on which Lemma 6 and Proposition 8 rest.
--
--   Differences from the source:
--   - generalization: every type S of the instance (label sets of codewords of C) → the label set of every balanced word a ∈ L_k; reason: C ⊆ L_k, so every type of the instance is covered
--   - encoding: the item set M of the instance (families Z, X, Y, G, P, Q, D_1..D_{n-2k-2}) → items Fin (n + 5k) decoded by index ranges into the families, D_t indexed from 0; reason: for n ≥ 2k + 2 the decoding is a bijection onto the paper's item set; it changes no instance
--   - encoding: multiples of k; strictly positive integers → ∃ z : ℤ, w(g) = k·z; ∃ z : ℤ, 0 < z ∧ v_S(g) = z (values are real numbers); reason: the same properties stated for real-valued weights and values
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, §2.1, PDF p. 8 (printed p. 7)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Instance

namespace MMSImpossibility.Goods

/-- §2.1 (PDF p. 8), for `n ≥ 2^16`, `k = 8⌈log₂ n⌉` and every type `S = S(a)` of a
balanced word `a ∈ L_k`, all clauses:
1. `∑_{j ∈ S} x_j = U`;
2. `n ≥ 2k + 2` (so the `D_t` are well defined);
3. every auxiliary weight is strictly positive and a multiple of `k`;
4. the total auxiliary weight is `nT`;
5. the correction function summed over all items is `0`;
6. every item value `v_S(g)` is a strictly positive integer;
7. the proportional share `v_S(M)/n` equals `µ = 3T`, and `µ = 204k³`. -/
theorem construction_facts (n : ℕ) (hn : 2 ^ 16 ≤ n) (a : Fin (kOf n) → Fin 2)
    (ha : a ∈ balancedWords (kOf n)) :
    ∑ j ∈ labelSet a, xw (kOf n) j = Uw (kOf n) ∧
    2 * kOf n + 2 ≤ n ∧
    (∀ i : Fin (n + 5 * kOf n), 0 < weight (decode n (kOf n) i) ∧
      ∃ z : ℤ, weight (decode n (kOf n) i) = (kOf n : ℝ) * z) ∧
    weightB (Finset.univ : Finset (Fin (n + 5 * kOf n))) = (n : ℝ) * Tw (kOf n) ∧
    corrB (labelSet a) (Finset.univ : Finset (Fin (n + 5 * kOf n))) = 0 ∧
    (∀ i : Fin (n + 5 * kOf n), ∃ z : ℤ, 0 < z ∧
      itemValue (labelSet a) (decode n (kOf n) i) = z) ∧
    (∑ i : Fin (n + 5 * kOf n), itemValue (labelSet a) (decode n (kOf n) i)) / n
      = mu (kOf n) ∧
    mu (kOf n) = 204 * (kOf n : ℝ) ^ 3 := by sorry

end MMSImpossibility.Goods
