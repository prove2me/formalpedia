-- Prove2me | Theorems.Thm_LEDPCount_lemma_3_2_gH_bound
-- name    : LEDPCount.lemma_3_2_gH_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:18.415851+00:00
-- url     : https://prove2.me/theorems/2f26eba1-8727-40c3-9b80-a664164520c9
-- title:
--   Proof of Lemma 3.2 — $g_H(n,c)\le 2^{\binom c2}(k!/(k-c)!)^2n^{2k-c}$
-- statement:
--   Let $H$ have $k$ vertices and $\ell\ge1$ edges, $n\ge k$ and $3\le c\le k$.
--   1. For each $C\subseteq E(K_n)$ with $2\le|C|\le\ell$ and $|V(C)|=c$, the number of pairs of injections $(\phi,\phi')$ with $C\subseteq\phi(E(H))\cap\phi'(E(H))$ is at most $\bigl(\tfrac{k!}{(k-c)!}n^{k-c}\bigr)^2$.
--   2. The number of such sets $C$ is at most $2^{\binom c2}n^c$.
--   3. Consequently
--   $$
--   g_H(n,c)\le 2^{\binom c2}\Bigl(\frac{k!}{(k-c)!}\Bigr)^2n^{2k-c}.
--   $$
--
--   Differences from the source:
--   - encoding: Algorithm 1 for a pattern on k vertices and an n-vertex graph → n ≥ k assumed; reason: line 11's (n − k)! is undefined for n < k; Theorem 1.1's setting
--   - encoding: k!/(k − c)! → Nat.descFactorial k c; reason: equal for c ≤ k
--   - encoding: E(K_n) → unordered pairs of Fin n that are not diagonal; reason: the edges of the complete graph
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), proof of Lemma 3.2, bound on g_H, p.20–21 (PDF p.22–23)

import Mathlib
import Definitions.Def_LEDPCount_gH

namespace LEDPCount

/-- Proof of Lemma 3.2, bound on `g_H(n, c)` (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.20–21, PDF p.22–23): for a
pattern with `k` vertices and `ℓ ≥ 1` edges, `n ≥ k` and `3 ≤ c ≤ k`:
1. for each `C ⊆ E(K_n)` with `2 ≤ |C| ≤ ℓ` and `|V(C)| = c`, the number of pairs `(ϕ, ϕ')` of
   injections with `C ⊆ ϕ(E(H)) ∩ ϕ'(E(H))` is at most `((k!/(k−c)!) n^{k−c})²`;
2. the number of such `C` is at most `2^{C(c,2)} n^c`;
3. `g_H(n, c) ≤ 2^{C(c,2)} (k!/(k−c)!)² n^{2k−c}`.

**Formalization Note** `k!/(k−c)!` is `Nat.descFactorial k c`. -/
theorem lemma_3_2_gH_bound {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) (n : ℕ) (hkn : k ≤ n) (c : ℕ) (hc3 : 3 ≤ c) (hck : c ≤ k) :
    (∀ C ∈ gIndex H n c, (gPairs H C).card ≤ (Nat.descFactorial k c * n ^ (k - c)) ^ 2) ∧
    (gIndex H n c).card ≤ 2 ^ (c.choose 2) * n ^ c ∧
    gH H n c ≤ 2 ^ (c.choose 2) * (Nat.descFactorial k c) ^ 2 * n ^ (2 * k - c) := by sorry

end LEDPCount
