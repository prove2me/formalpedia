-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_lemma_5_5
-- name    : MultStretchAPASP.Weighted.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:11:01.20868+00:00
-- url     : https://prove2.me/theorems/6e7803c4-976b-4425-b45c-fab068de15da
-- title:
--   Lemma 5.5 — the output of Algorithm 10 has stretch 2: d[u, v] ≤ 2δ(u, v)
-- statement:
--   Let $G=(V,E,w)$ be an undirected graph on $n$ vertices whose edge weights are positive integers at most $W_{\max}$, and let $d$ be the table output by Algorithm 10 on $G$ (for any sample $S_1$, any choice of pivots, any order of the loops and any admissible outputs of the approximation subroutines). Then
--   $$d[u,v]\ \le\ 2\,\delta(u,v)\qquad\text{for all }(u,v)\in V\times V,$$
--   with $2\cdot\infty=\infty$.
--
--   This is the upper half of the correctness of Algorithm 10; the case analysis on the number of path edges outside $E_1$ is where the offset-shifted products of lines 12–27 are needed.
--
--   Differences from the source:
--
--   - encoding: an undirected graph G = (V, E, w) with w : E → ℝ≥0 → a symmetric weight matrix w : Fin n → Fin n → ℝ≥0∞ with ⊤ on the diagonal (IsWGraph), w x y = ⊤ meaning no edge; distances δ in ℝ≥0∞ (⊤ for disconnected pairs); reason: same graphs; ℝ≥0∞ represents the paper's ∞ exactly, so no junk value arises for disconnected pairs
--   - encoding: §5: edge weights are positive integers in [W_max] ∪ {∞} → IsIntWGraph Wmax w: every finite entry of the weight matrix is a natural number k with 1 ≤ k ≤ Wmax; reason: the §5 standing assumption, with ∞ = no edge
--   - reading: the output of Algorithm 10 (a randomized algorithm calling black boxes) → every possible output of the relational process Alg10Run: for every sample S₁ ⊆ V, every pivot map, every order of the sequential foreach loops, and every admissible output of the (1 + ε)-MSASP of line 10 and of the (1 + ε)-approximate (min, +)-products of line 11 and Algorithm 9 (tables with values in ℝ≥0∞); reason: the proof argues for every outcome of S₁ and uses only the guarantees of the black boxes; quantifying over every run is the strongest reading
--   - encoding: Algorithm 10 when the sample S₁ is empty (p undefined) → Alg10Run skips lines 5–8 and 10–27 and uses E₁ = E: the run is Algorithm 4's table followed by the four calls of Algorithm 5 of lines 9 and 28; reason: with no sources line 10 and line 11 change nothing and there are no pivots or buckets; S₁ = ∅ has positive probability
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 23, Lemma 5.5

import Mathlib
import Definitions.Def_MultStretchAPASP_Weighted_Graph
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus
import Definitions.Def_MultStretchAPASP_Weighted_Alg10

set_option autoImplicit false

open scoped ENNReal

namespace MultStretchAPASP.Weighted

/-- **Lemma 5.5** (p. 23). Every possible output `d` of Algorithm 10 satisfies `d[u, v] ≤ 2·δ(u, v)` for all
`(u, v) ∈ V × V`: for every undirected graph `w` on `Fin n` with positive integer weights at most
`Wmax` (§5), every sample `S₁ = S`, every pivot map, every order of the loops and every
admissible output of the approximation black boxes (`Alg10Run`). -/
theorem lemma_5_5 {n : ℕ} (Wmax : ℕ) (w : WMat n) (hw : IsIntWGraph Wmax w)
    (S : Finset (Fin n)) (d : Table n) (hd : Alg10Run w Wmax S d) (u v : Fin n) :
    d u v ≤ 2 * dist w u v := by sorry

end MultStretchAPASP.Weighted
