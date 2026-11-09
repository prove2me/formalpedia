-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_lemma_6
-- name    : MMSImpossibility.Goods.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:17:57.19697+00:00
-- url     : https://prove2.me/theorems/cb8092cb-09d4-4f65-abf6-b6e223b4b145
-- title:
--   Lemma 6 — every agent's maximin share is exactly $\mu$
-- statement:
--   Throughout, $n \ge 2^{16}$, $k = 8\lceil \log_2 n\rceil$, and the instance of §2.1 has $m = n+5k$ goods: $Z_j, X_j, Y_j$ ($0\le j<2k$), $G_h$ ($0\le h<k$), $P$, $Q$ and $D_t$ ($1\le t\le n-2k-2$), with auxiliary weights $w$ and, for an agent of type $S$, valuation $v_S(g) = 3w(g)+\rho_S(g)$ (equation (3)); $\mu = 3T = 204k^3$ and $\ell = k/24$.
--
--   Let each agent $i$ have the type $S(\sigma_i)$ of a balanced word $\sigma_i\in L_k$. Then every agent's maximin share, over partitions of all $n+5k$ goods into $n$ bundles, is
--
--   $$\mathrm{MMS}_i = \mu = 3T = 204k^3.$$
--
--   Together with Proposition 8 this turns an additive shortfall of $k/24$ into the relative shortfall of Theorem 1.
--
--   Differences from the source:
--   - generalization: agents with distinct types drawn from the code C → any assignment σ of balanced words (not necessarily distinct, no distance assumed); reason: the paper's assignment is one instance; MMS_i depends only on agent i's own type
--   - encoding: the item set M of the instance (families Z, X, Y, G, P, Q, D_1..D_{n-2k-2}) → items Fin (n + 5k) decoded by index ranges into the families, D_t indexed from 0; reason: for n ≥ 2k + 2 the decoding is a bijection onto the paper's item set; it changes no instance
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, Lemma 6, PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Instance

namespace MMSImpossibility.Goods

open LittleCharity.MMS

/-- Lemma 6 (PDF p. 9): for `n ≥ 2^16`, `k = 8⌈log₂ n⌉` and any assignment `σ` of balanced
words to the agents, every agent's maximin share (over partitions of all `n + 5k` items into
`n` bundles) is exactly `µ = 3T`. -/
theorem lemma_6 (n : ℕ) (hn : 2 ^ 16 ≤ n) (σ : Fin n → (Fin (kOf n) → Fin 2))
    (hσ : ∀ i, σ i ∈ balancedWords (kOf n)) (i : Fin n) :
    mms (valuation n σ i) n Finset.univ = mu (kOf n) := by sorry

end MMSImpossibility.Goods
