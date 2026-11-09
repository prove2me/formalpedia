-- Prove2me | Theorems.Thm_HypClass1_proposition_4_8
-- name    : HypClass1.proposition_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:34:50.480431+00:00
-- url     : https://prove2.me/theorems/73c41e7f-087b-4c40-be09-02ba703b8cb3
-- title:
--   Proposition 4.8 — deleting $\le\eta n$ vertices keeps $(\varepsilon+4\eta/p)$-pseudorandomness
-- statement:
--   Let $\varepsilon, p \in [0,1]$ and $\eta \in [0, 1/2]$. Let $H$ be an $(\varepsilon,p,n)$-pseudorandom 3-graph on a vertex set $V$ of size $n$, and let $D \subseteq V$ with $|D| \le \eta n$. Then the induced subhypergraph $\tilde H = H[V \setminus D]$ is
--   $$
--   \left(\varepsilon + \frac{4\eta}{p},\ p,\ n - |D|\right)\text{-pseudorandom}.
--   $$
--
--   **Formalization Note** $V$ is a finite subset $W$ of `Fin N`; $H[W \setminus D]$ is the set of edges of $H$ contained in $W \setminus D$. The hypothesis $p > 0$ is added.
--
--   Differences from the source:
--   - encoding: p ∈ [0, 1] → 0 < p ≤ 1; reason: the error parameter ε + 4η/p is undefined at p = 0; this excludes only the undefined case
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Proposition 4.8, p.10

import Mathlib
import Definitions.Def_HypClass1_IsPseudorandom3

namespace HypClass1

/-- **Proposition 4.8 (deleting few vertices keeps pseudorandomness).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Proposition 4.8, p.10:
"Let ε, p ∈ [0, 1] and η ∈ [0, 1/2] be real numbers. Let H be an (ε, p, n)-pseudorandom 3-graph on n
vertices and let D ⊆ V be a subset of vertices such that |D| ≤ ηn. Then the induced subhypergraph
H̃ := H[V ∖ D] is (ε + 4η/p, p, n − |D|)-pseudorandom."

**Formalization Note.** The vertex set is a finite set `W` (here `V`) of `Fin N`, `n = |W|`; the induced
subhypergraph `H[W ∖ D]` is the set of edges of `H` contained in `W ∖ D`, a 3-graph on `W ∖ D` with
`|W ∖ D| = n − |D|`. `p > 0` is assumed: at `p = 0` the parameter `4η/p` is undefined. -/
theorem proposition_4_8 {N : ℕ} (ε p η : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) (W : Finset (Fin N)) (H : Finset (Finset (Fin N)))
    (hH : IsPseudorandom3 ε p W H) (D : Finset (Fin N)) (hDW : D ⊆ W)
    (hD : (D.card : ℝ) ≤ η * W.card) :
    IsPseudorandom3 (ε + 4 * η / p) p (W \ D) (H.filter (fun e => e ⊆ W \ D)) := by sorry

end HypClass1
