-- Prove2me | Theorems.Thm_LooseHamHitting_Main_theorem_5_1
-- name    : LooseHamHitting.Main.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:18:56.40389+00:00
-- url     : https://prove2.me/theorems/63d597b8-e3fa-4fc6-90ee-e2919788697c
-- title:
--   Theorem 5.1 (Kahn) — entropy inequality for random perfect matchings of a 3-graph
-- statement:
--   Let $G$ be a 3-graph on $n$ vertices with $3\mid n$, and let $F$ be a random perfect matching of $G$ with an arbitrary law. For a vertex $u$ let $F(u)$ be the edge of $F$ containing $u$; for $e\in G$ let $p_e=P[e\in F]$ and $\gamma_e=P[\exists f\in F:|e\cap f|\ge2]$. There are absolute constants $C_1,C_2>0$ such that always
--   $$H[F]\le\frac13\sum_uH[F(u)]-\frac{2n}3+C_1\sum_u\sum_{e\ni u}p_e\sqrt{\gamma_e}+C_2\log n.$$
--
--   This is Kahn's inequality ([25, Theorem 4.2]), which drives the entropy stability results of §§5–6.
--
--   Differences from the source:
--   - encoding: two O(·) terms → absolute constants C₁, C₂ > 0, valid for every n; reason: for bounded n the difference of the two sides is bounded and log n ≥ log 3 > 0 (n = 0 is trivial), so this is equivalent to the asymptotic reading
--   - encoding: F(u), the edge of F containing u → the set of edges of F containing u (a singleton); reason: injective encoding of the same random variable; entropy unchanged
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 17, Theorem 5.1 (citing Kahn [25, Theorem 4.2])

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Entropy
import Definitions.Def_LooseHamHitting_Main_Marginals

set_option autoImplicit false

open Classical

namespace LooseHamHitting.Main

/-- Theorem 5.1 (Kahn [25, Theorem 4.2]): entropy inequality for a random perfect matching of a
3-graph, with absolute constants `C₁, C₂` for the two `O(·)` terms. -/
theorem theorem_5_1 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (β : Type*) (V : Finset β) (G : Finset (Finset β)) (μ : Finset (Finset β) → ℝ) (n : ℕ),
        V.card = n → IsThreeGraph V G → 3 ∣ n → IsLawOn (perfectMatchings V G) μ →
        lawEntropy (perfectMatchings V G) μ id ≤
          1 / 3 * ∑ u ∈ V, lawEntropy (perfectMatchings V G) μ (fun F => edgeAt F u) -
            2 * (n : ℝ) / 3 +
            C₁ * ∑ u ∈ V, ∑ e ∈ G.filter (fun e => u ∈ e),
              pmEdgeProb V G μ e * Real.sqrt (pmOverlapProb V G μ e) +
            C₂ * Real.log n := by sorry

end LooseHamHitting.Main
