-- Prove2me | Theorems.Thm_MetricTSPSublinear_lemma_5_5
-- name    : MetricTSPSublinear.lemma_5_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:32:44.396671+00:00
-- url     : https://prove2.me/theorems/923b12dc-5920-4abe-bf88-cf6530a89773
-- title:
--   Lemma 5.5: core alignment
-- statement:
--   Let $d$ be a metric on $V$ with MST $T$ (edge set $E$), $M=w(T)$, $K$ the cut LP value and $D=M-K$. Let $S\subseteq V$ be the core terminals, and let the computed core be represented by a finite weighted tree $K_C$ (a subdivision of $R(C)$) whose leaves are images of terminals, with a non-expansive map $q:V\to V(K_C)$, $d_{K_C}(q_u,q_v)\le d(u,v)$, and with weight $w(K_C)\ge K(S)-\eta$. Let $T_1$ be a dominated shortening of $T$ with total shortening $\sum_e(w_T(e)-w_{T_1}(e))\le\beta$.
--
--   Then there are an **aligned core** $C^*$, obtained from $K_C$ by lowering edge weights (the removed weight is $w(B)=w(K_C)-w(C^*)$), and a shortening $T^*$ of $T_1$ such that:
--   1. $T^*$ agrees with $T_1$ outside the core subtree $T\langle S\rangle$, and $w(T^*\langle S\rangle)=w(C^*)$, with $w_{T^*}(uv)=d_{C^*}(q_u,q_v)$ on its edges;
--   2. $d_{C^*}(q_u,q_v)\le d_{T^*}(u,v)$ for all $u,v$, with equality when $u,v$ are vertices of $T\langle S\rangle$;
--   3. $w(B)\le 2D+\eta+\beta$ and $w(T_1)-w(T^*)\le 4D+2\eta+\beta$;
--   4. $T^*$ is a dominated shortening of $T$.
--
--   With $\eta=0$ and $\beta=4D+\varepsilon\widehat M$ (Lemma 5.2) this gives the paper's bounds $w(B)\le6D+\varepsilon\widehat M$ and $w(T_1)-w(T^*)\le 8D+\varepsilon\widehat M$. The lemma lets the analysis compare the computed core, which the algorithm knows, with the core part of the MST shortening, which it does not.
--
--   **Formalization Note** The continuous core $R(C)$ with zeroed segments $B$ is replaced by a finite subdivision whose edge weights are lowered; partial lowering of an edge plays the role of zeroing part of it.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §5.4, Lemma 5.5 and its proof, pp.19–21 (PDF pp.21–23).

import Mathlib
import Definitions.Def_TreeCoverLB_WeightedTree
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_IsMSTOf
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSPSublinear_hull
import Definitions.Def_MetricTSPSublinear_treeDist
import Definitions.Def_MetricTSPSublinear_IsDominatedShortening

open scoped Classical

namespace MetricTSPSublinear

/-- **Lemma 5.5 (Core Alignment), discrete form.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two
Approximation*, arXiv:2611.04283, §5.4, pp.19–21 (PDF pp.21–23): "There exists a collection of core segments B and a
dominated shortening T* of T1 such that: 1. w(T*⟨S⟩) = w(C*) = K(S) − w(B). 2. … d_{C*}(q_u, q_v) ≤ d_{T*}(u, v).
Furthermore, this holds with equality for vertices in the core subtree T1⟨S⟩. 3. Every edge outside T1⟨S⟩ has the
same weight in T* as it does in T1. … w(B) ≤ 6D + εM̂ and w(T1) − w(T*) ≤ 8D + εM̂."

The core is a subdivision `K` of `R(C)` (leaves are terminals), `q` is non-expansive, `K` has weight at least
`K(S) − η`, and `w1` (= T1) is a dominated shortening of the MST `E` with total shortening at most `β`
(the paper: η = 0, β = 4D + εM̂). The aligned core `C*` is `K` with lowered weights (`w(B) = w(K) − w(C*)`). -/
theorem lemma_5_5 {n m : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (E : Finset (Sym2 (Fin n))) (hE : DoublingMST.IsMSTOf d Finset.univ E)
    (S : Finset (Fin n)) (K : TreeCoverLB.WeightedTree (Fin m)) (q : Fin n → Fin m)
    (hq : ∀ u v, K.dist (q u) (q v) ≤ d u v)
    (hleaf : ∀ c, (∀ y₁ y₂, K.G.Adj c y₁ → K.G.Adj c y₂ → y₁ = y₂) → ∃ s ∈ S, q s = c)
    (η : ℝ) (hK : cutLP d S - η ≤ ∑ f ∈ K.G.edgeFinset, K.w f)
    (w1 : Sym2 (Fin n) → ℝ) (hw1 : IsDominatedShortening d E w1)
    (β : ℝ) (hT1 : ∑ e ∈ E, (DoublingMST.edgeCost d e - w1 e) ≤ β) :
    ∃ (C : TreeCoverLB.WeightedTree (Fin m)) (wT : Sym2 (Fin n) → ℝ),
      -- the aligned core `C*`: `K` with smaller weights
      C.G = K.G ∧ (∀ f ∈ K.G.edgeSet, C.w f ≤ K.w f) ∧
      -- the comparison tree `T*`: a shortening of `T1`
      (∀ e ∈ E, 0 ≤ wT e ∧ wT e ≤ w1 e) ∧
      -- property 3: edges outside `T⟨S⟩` keep their `T1`-weight
      (∀ e ∈ E, e ∉ hull E S → wT e = w1 e) ∧
      -- definition of `T*` on hull edges
      (∀ u v, s(u, v) ∈ hull E S → wT s(u, v) = C.dist (q u) (q v)) ∧
      -- property 1: `w(T*⟨S⟩) = w(C*)`
      ∑ e ∈ hull E S, wT e = ∑ f ∈ K.G.edgeFinset, C.w f ∧
      -- property 2: domination, with equality on `T⟨S⟩`
      (∀ u v, C.dist (q u) (q v) ≤ treeDist E wT u v) ∧
      (∀ u v, (u ∈ S ∨ ∃ e ∈ hull E S, u ∈ e) → (v ∈ S ∨ ∃ e ∈ hull E S, v ∈ e) → C.dist (q u) (q v) = treeDist E wT u v) ∧
      -- `w(B) ≤ 2D + η + β`
      ∑ f ∈ K.G.edgeFinset, K.w f - ∑ f ∈ K.G.edgeFinset, C.w f ≤
        2 * (DoublingMST.mstWeight d - cutLP d Finset.univ) + η + β ∧
      -- `w(T1) − w(T*) ≤ 4D + 2η + β`
      ∑ e ∈ E, (w1 e - wT e) ≤ 4 * (DoublingMST.mstWeight d - cutLP d Finset.univ) + 2 * η + β ∧
      IsDominatedShortening d E wT := by sorry

end MetricTSPSublinear
