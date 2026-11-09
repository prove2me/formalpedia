-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_final_distance
-- name    : MMSImpossibility.Goods.final_distance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:18:01.469002+00:00
-- url     : https://prove2.me/theorems/f1fe3956-63f0-43cc-ab7f-59b2918e8f27
-- title:
--   Proof of Proposition 8, "The final distance contradiction" — $|S_Q\setminus S_P| \le 4d+\ell < k/4$
-- statement:
--   Throughout, $n \ge 2^{16}$, $k = 8\lceil \log_2 n\rceil$, and the instance of §2.1 has $m = n+5k$ goods: $Z_j, X_j, Y_j$ ($0\le j<2k$), $G_h$ ($0\le h<k$), $P$, $Q$ and $D_t$ ($1\le t\le n-2k-2$), with auxiliary weights $w$ and, for an agent of type $S$, valuation $v_S(g) = 3w(g)+\rho_S(g)$ (equation (3)); $\mu = 3T = 204k^3$ and $\ell = k/24$.
--
--   Setting of the proof of Proposition 8: each agent $i$ has the type $S_i = S(\sigma_i)$ of a balanced word $\sigma_i \in L_k$, the words are pairwise distinct, and $(B_1,\dots,B_n)$ is an allocation in which every agent receives $v_{S_i}(B_i) \ge \mu - \ell$. Let $B_P$, $B_Q$ be the bundles containing $P$ and $Q$, and $S_P$, $S_Q$ the types of their recipients. With $I_Q = \{j\in S_Q : Y_j\in B_Q\}$, $d = k-|I_Q|$ and $R = \{j\in S_Q : X_j\in B_P\}$,
--
--   $$|S_Q\setminus S_P| \le |S_Q\setminus R| + |R\setminus S_P| \le 3d + (d+\ell) = 4d+\ell \le 5\ell = \frac{5k}{24} < \frac k4,$$
--
--   with every link of the chain: $|S_Q\setminus R| \le 3d$, $|R\setminus S_P| \le d+\ell$, $4d+\ell\le 5\ell$, $5\ell = 5k/24$ and $5k/24 < k/4$.
--
--   The recipients of $P$ and $Q$ would have types closer than the code's distance allows.
--
--   Differences from the source:
--   - generalization: agent types are label sets of distinct codewords chosen from the code C of Lemma 5 → any injective assignment σ of balanced words in L_k; the code's distance and size are not assumed; reason: C ⊆ L_k and the codewords are distinct, so the paper's assignment is one instance; this step of the proof uses no distance property
--   - encoding: the item set M of the instance (families Z, X, Y, G, P, Q, D_1..D_{n-2k-2}) → items Fin (n + 5k) decoded by index ranges into the families, D_t indexed from 0; reason: for n ≥ 2k + 2 the decoding is a bijection onto the paper's item set; it changes no instance
--   - encoding: an allocation (B_1, …, B_n), an ordered partition of M into possibly empty bundles → a map A : Fin (n + 5k) → Fin n with B_i = A⁻¹(i); reason: the two describe the same objects (every item allocated, bundles may be empty)
--   - encoding: B_P, B_Q the bundles containing P and Q → the bundles of agents A p and A q, where p, q are the item indices decoding to P and Q; reason: p and q are the unique such indices; same bundles
--   - encoding: the counts |·| and d mixed with ℓ = k/24 → counts and d cast to ℝ; reason: ℓ is not an integer; the casts change no value
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, proof of Proposition 8, paragraph "The final distance contradiction", PDF p. 12 (printed p. 11)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Instance

namespace MMSImpossibility.Goods

/-- Proof of Proposition 8, "The final distance contradiction" (PDF p. 12), in the setting
of the proof of Proposition 8 (as for equation (4)), with `S_P`, `S_Q` the types of the
recipients of `B_P`, `B_Q`, `R = {j ∈ S_Q : X_j ∈ B_P}`, `d = k - |I_Q|`, `ℓ = k/24`:
`|S_Q \ S_P| ≤ |S_Q \ R| + |R \ S_P| ≤ 3d + (d + ℓ) = 4d + ℓ ≤ 5ℓ = 5k/24 < k/4`. -/
theorem final_distance (n : ℕ) (hn : 2 ^ 16 ≤ n) (σ : Fin n → (Fin (kOf n) → Fin 2))
    (hσ : ∀ i, σ i ∈ balancedWords (kOf n)) (hinj : Function.Injective σ)
    (A : Fin (n + 5 * kOf n) → Fin n)
    (hA : ∀ i, mu (kOf n) - ell (kOf n) ≤ valuation n σ i (bundle A i))
    (p q : Fin (n + 5 * kOf n)) (hp : decode n (kOf n) p = Good.P)
    (hq : decode n (kOf n) q = Good.Q) :
    let SP := labelSet (σ (A p))
    let SQ := labelSet (σ (A q))
    let R := Rset SQ (bundle A (A p))
    let d : ℝ := (dCount SQ (bundle A (A q)) : ℝ)
    (((SQ \ SP).card : ℝ) ≤ ((SQ \ R).card : ℝ) + ((R \ SP).card : ℝ)) ∧
    (((SQ \ R).card : ℝ) ≤ 3 * d) ∧
    (((R \ SP).card : ℝ) ≤ d + ell (kOf n)) ∧
    (4 * d + ell (kOf n) ≤ 5 * ell (kOf n)) ∧
    5 * ell (kOf n) = 5 * (kOf n : ℝ) / 24 ∧
    5 * (kOf n : ℝ) / 24 < (kOf n : ℝ) / 4 := by sorry

end MMSImpossibility.Goods
