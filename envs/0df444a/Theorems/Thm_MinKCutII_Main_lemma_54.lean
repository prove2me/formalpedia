-- Prove2me | Theorems.Thm_MinKCutII_Main_lemma_54
-- name    : MinKCutII.Main.lemma_54
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:06.150879+00:00
-- url     : https://prove2.me/theorems/3eddb9b1-2d62-4eed-84e1-b7e9147970c2
-- title:
--   Lemma 54 — at most 2^{k−2} − 1 rooted cuts of value below λ_k/(k − 1) [GHLL22]
-- statement:
--   Let $G=(V,E,c)$ have positive capacities, let $2\le k\le|V|$, $\lambda=\lambda_k(G)$, and fix a root $r\in V$. Then
--   $$\#\Big\{S\subseteq V\setminus\{r\} : S\ne\emptyset,\ c_G(S)<\frac{\lambda}{k-1}\Big\}\ \le\ 2^{k-2}-1.$$
--   The bound limits the depth of the safe-contraction branching in the deterministic 4-cut algorithm.
--
--   Differences from the source:
--
--   - reading: a graph with |V(G)| ≥ k → 2 ≤ k ≤ |V|; reason: λ/(k − 1) and 2^{k−2} are meaningful only for k ≥ 2
--   - encoding: λ := λ_k(G) → a real L with lam G k = L; reason: λ_k is finite since k ≤ |V|
--   - generalization: a graph (positive integer capacities, §2) → positive real capacities; reason: integers are a special case; [GHLL22] is stated for weighted graphs
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 40, Lemma 54

import Mathlib
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Cuts

set_option autoImplicit false

open CombOpt.MinCut

namespace MinKCutII.Main

/-- **Lemma 54** (p. 40, [GHLL22]). Let `G` have positive capacities, `2 ≤ k ≤ |V|`, `λ = λ_k(G)`,
and fix a root `r`. At most `2^(k−2) − 1` distinct nonempty sets `S ⊆ V \ {r}` satisfy
`c_G(S) < λ/(k − 1)`. -/
theorem lemma_54 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (G : CapGraph V E)
    (k : ℕ) (hpos : PosCap G) (hk : 2 ≤ k) (hkn : k ≤ Fintype.card V) (L : ℝ)
    (hL : lam G k = (L : WithTop ℝ)) (r : V) :
    (Finset.univ.filter (fun S : Finset V =>
        S.Nonempty ∧ r ∉ S ∧ cutVal G S < L / ((k : ℝ) - 1))).card ≤ 2 ^ (k - 2) - 1 := by sorry

end MinKCutII.Main
