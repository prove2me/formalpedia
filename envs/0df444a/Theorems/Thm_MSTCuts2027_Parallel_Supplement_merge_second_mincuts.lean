-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_Supplement_merge_second_mincuts
-- name    : MSTCuts2027.Parallel.Supplement.merge_second_mincuts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:40:45.606161+00:00
-- url     : https://prove2.me/theorems/e32a7938-282c-430c-b6bf-495a2701ec90
-- title:
--   Theorem 5 — merging two MSTs of $G_2$ with $|V_1|$ second-mincut computations
-- statement:
--   Let $F$ be a symmetric real cut function on the vertex set $V=\{0,\dots,n-1\}$ for which every pair of distinct vertices has a second mincut. Let $V_1,V_2\subseteq V$ be disjoint, with $|V_1|\le|V_2|$, such that the mincut value of every pair of distinct vertices of $V_1$, and of every pair of distinct vertices of $V_2$, is greater than the mincut value of every pair in $V_1\times V_2$:
--   $$\lambda_1(x,y)<\lambda_1(a,b)\qquad\text{for all } x\in V_1,\ y\in V_2 \text{ and distinct } a,b \text{ both in } V_1 \text{ or both in } V_2.$$
--   Let $\mathcal C$ be a set of cuts containing a mincut and a second mincut of every pair of distinct vertices of $V_1$ and of every pair of distinct vertices of $V_2$. Let $T_1,T_2$ be MSTs of $G_2[V_1]$ and $G_2[V_2]$. Then there is a set $P\subseteq V_1\times V_2$ with $|P|=|V_1|$ such that:
--
--   1. for every choice of a second mincut $S(q)$ of each pair $q\in P$, the set $\mathcal C\cup\{S(q):q\in P\}$ contains a second $(x,y)$-mincut for every $x\in V_1$, $y\in V_2$;
--   2. a maximum spanning tree of the graph on $V_1\cup V_2$ with edge set $T_1\cup T_2\cup P$ (capacities $\lambda_2$) exists, and every such tree is an MST of $G_2[V_1\cup V_2]$;
--   3. all pairs of $V_1\times V_2$ have the same mincut value.
--
--   This is the second-mincut version of Theorem 2 of the base mission: merging two trees costs $|V_1|$ second-mincut computations, provided the sets are picked in decreasing order of the mincut values between them.
--
--   Differences from the source:
--   - reading: P ⊂ V1 × V2 → P ⊆ V1 × V2; reason: §2 uses ⊂ for subsets (X ⊂ V); a proper subset is impossible when |V1| = |V2| = 1, where |P| = 1 = |V1 × V2|
--   - encoding: second mincut for each pair in P plus C is a second mincut cover → for every choice of a second mincut of each pair in P; reason: the paper does not fix which second mincut is computed for a pair
--   - encoding: an MST on edges T1 ∪ T2 ∪ P is an MST for G2[V1 ∪ V2] → such a maximum spanning tree exists, and every one is an MST of G2[V1 ∪ V2]; reason: same statement, with the existence that 'an MST' presupposes made explicit
--   - encoding: C contains the mincut cover and second mincut cover of the pairs inside V1 and inside V2 → C contains a mincut and a second mincut of each such pair of distinct vertices, and possibly more cuts; reason: definition of a (second) mincut cover
--   - encoding: without loss of generality |V1| ≤ |V2| → hypothesis |V1| ≤ |V2|; reason: the conclusion |P| = |V1| is stated under it
--   - encoding: vertex set V → Fin n; reason: the published graph mergeGraph of the base mission is on Fin n; every finite vertex set is in bijection with some Fin n
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Theorem 5, printed p. 15, PDF p. 17

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms
import Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondCutModel
import Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondAlgorithms

namespace MSTCuts2027.Parallel.Supplement

open MSTCuts2027.Parallel

/-- Theorem 5: merging for second mincuts. Under strict separation of the mincut values, there is
`P ⊆ V₁ × V₂` with `|P| = |V₁|` such that (1) second mincuts of the pairs of `P`, chosen in any
way, together with `C` cover all pairs of `V₁ × V₂`; (2) a maximum spanning tree on
`T₁ ∪ T₂ ∪ P` exists, and every one is an MST of `G₂[V₁ ∪ V₂]`; (3) all pairs of `V₁ × V₂` have
the same mincut value. -/
theorem merge_second_mincuts (n : ℕ) (F : Finset (Fin n) → ℝ) (hF : IsSymmetricCutFunction F)
    (hex : SecondMincutsExist F) (V₁ V₂ : Finset (Fin n)) (hdisj : Disjoint V₁ V₂)
    (h₁ : ∀ a ∈ V₁, ∀ b ∈ V₁, a ≠ b → ∀ x ∈ V₁, ∀ y ∈ V₂, lam F x y < lam F a b)
    (h₂ : ∀ a ∈ V₂, ∀ b ∈ V₂, a ≠ b → ∀ x ∈ V₁, ∀ y ∈ V₂, lam F x y < lam F a b)
    (C : Set (Finset (Fin n)))
    (hC₁ : ∀ a ∈ V₁, ∀ b ∈ V₁, a ≠ b →
      (∃ D ∈ C, IsMincut F a b D) ∧ ∃ D ∈ C, IsSecondMincut F a b D)
    (hC₂ : ∀ a ∈ V₂, ∀ b ∈ V₂, a ≠ b →
      (∃ D ∈ C, IsMincut F a b D) ∧ ∃ D ∈ C, IsSecondMincut F a b D)
    (T₁ : SimpleGraph {y // y ∈ V₁}) (T₂ : SimpleGraph {y // y ∈ V₂})
    (hT₁ : IsMST2On F V₁ T₁) (hT₂ : IsMST2On F V₂ T₂) (hcard : V₁.card ≤ V₂.card) :
    ∃ P : Finset (Fin n × Fin n), P ⊆ V₁ ×ˢ V₂ ∧ P.card = V₁.card ∧
      (∀ S : Fin n × Fin n → Finset (Fin n), (∀ q ∈ P, IsSecondMincut F q.1 q.2 (S q)) →
        ∀ x ∈ V₁, ∀ y ∈ V₂,
          ∃ D ∈ C ∪ ((P.image S : Finset (Finset (Fin n))) : Set (Finset (Fin n))),
            IsSecondMincut F x y D) ∧
      (∃ T, FlowsNetworks.MultiTerminal.IsMaximalSpanningSubtree (mergeGraph T₁ T₂ P) T
          (capacity2On F (V₁ ∪ V₂))) ∧
      (∀ T, FlowsNetworks.MultiTerminal.IsMaximalSpanningSubtree (mergeGraph T₁ T₂ P) T
          (capacity2On F (V₁ ∪ V₂)) → IsMST2On F (V₁ ∪ V₂) T) ∧
      (∀ x ∈ V₁, ∀ x' ∈ V₁, ∀ y ∈ V₂, ∀ y' ∈ V₂, lam F x y = lam F x' y') := by sorry

end MSTCuts2027.Parallel.Supplement
