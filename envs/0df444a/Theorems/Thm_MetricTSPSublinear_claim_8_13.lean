-- Prove2me | Theorems.Thm_MetricTSPSublinear_claim_8_13
-- name    : MetricTSPSublinear.claim_8_13
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:36:54.634477+00:00
-- url     : https://prove2.me/theorems/a96f4ad9-a2f1-4762-8e12-33e88baf02ff
-- title:
--   Claim 8.13: optimal fragment shortenings retain the hanging weight
-- statement:
--   Let $d$ be a symmetric distance on $V$ and $E$ the edge set of a spanning tree $T$ with weights $w_T(e)=d(e)$. Let $U$ be a dominated shortening of $T$ ($0\le U\le w_T$ on $E$ and $d_U\le d$), and put $D_U=\sum_{e\in E}(w_T(e)-U(e))$. Let $F_j$ ($j\in J$) be disjoint cell fragments with roots $o_j$, and for each $j$ let $t_j$ be an admissible shortening of $F_j$ (constraints (10) with parameters $\lambda\ge1$, $r$) of maximum total weight. Let $H$ be a set of edges such that
--   1. every edge of $E$ outside $H$ lies inside some fragment;
--   2. if $v\in F_j$ is incident to an edge of $T$ leaving $F_j$, the $T$-path from $v$ to $o_j$ lies in $H$;
--   3. every $v\in F_j$ is within $U$-distance $r$ of some $a\in F_j$ whose $T$-path to $o_j$ lies in $H$.
--
--   Writing $A_H=\sum_j\sum_{e\in E\cap H}t_j(e)$,
--   $$\sum_j w(t_j)\ \ge\ w_T(E\setminus H)+\Bigl(1-\frac1\lambda\Bigr)A_H-2D_U .$$
--
--   In the analysis of contracted cells, $H$ collects the core, the removed hanging edges and the regular-cell hanging parts, so the right side says the optimal local shortenings retain essentially all MST weight outside $H$ and most of their own weight inside $H$.
--
--   **Formalization Note** The discretization loss $n\sigma$ of the paper is not part of this statement.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §8.2, Claim 8.13 and its proof, pp.30–31 (PDF pp.32–33).

import Mathlib
import Definitions.Def_DoublingMST_edgeCost
import Definitions.Def_MetricTSPSublinear_treeDist
import Definitions.Def_MetricTSPSublinear_IsAdmissibleFragShortening

open scoped Classical

namespace MetricTSPSublinear

/-- **Claim 8.13 (without the discretization term).** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two
Approximation*, arXiv:2611.04283, §8.2, pp.30–31 (PDF pp.32–33): "The local shortenings satisfy
Σ_{P : contracted} A_P ≥ w_T(T \ H) + (1 − 1/λ) A_H − 2D_U − nσ."

Here `t j` are optimal admissible shortenings (10) of the fragments `F j` (roots `o j`) of the tree `E`, `U` is a
dominated shortening of `E` with `D_U = Σ (w_T − U)`, `H` is an edge set such that every edge outside `H` lies inside a
fragment (hH1), boundary vertices of fragments have their root path in `H` (hH2), and every fragment vertex is within
`U`-distance `r` of a fragment vertex whose root path lies in `H` (hH3); `A_H = Σ_j Σ_{e ∈ H} t_j(e)`.

**Formalization Note.** The rounding to multiples of `σ` (the `nσ` term) is omitted; it is a separate, elementary step. -/
theorem claim_8_13 {n : ℕ} {ι : Type*} [Fintype ι] (d : Fin n → Fin n → ℝ) (hsymm : ∀ u v, d u v = d v u)
    (E : Finset (Sym2 (Fin n))) (hT : (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).IsTree)
    (U : Sym2 (Fin n) → ℝ) (hU : ∀ e ∈ E, 0 ≤ U e ∧ U e ≤ DoublingMST.edgeCost d e)
    (hUd : ∀ u v, treeDist E U u v ≤ d u v)
    (F : ι → Finset (Fin n)) (hF : Pairwise fun j k => Disjoint (F j) (F k)) (o : ι → Fin n)
    (H : Finset (Sym2 (Fin n))) (lam r : ℝ) (hlam : 1 ≤ lam)
    (hH1 : ∀ e ∈ E, e ∉ H → ∃ j, ∀ z ∈ e, z ∈ F j)
    (hH2 : ∀ j b c, s(b, c) ∈ E → b ∈ F j → c ∉ F j → pathEdges E b (o j) ⊆ H)
    (hH3 : ∀ j, ∀ v ∈ F j, ∃ a ∈ F j, pathEdges E a (o j) ⊆ H ∧ treeDist E U v a ≤ r)
    (t : ι → Sym2 (Fin n) → ℝ) (ht : ∀ j, IsAdmissibleFragShortening d E (F j) (o j) lam r (t j))
    (hopt : ∀ j t', IsAdmissibleFragShortening d E (F j) (o j) lam r t' → ∑ e ∈ E, t' e ≤ ∑ e ∈ E, t j e) :
    ∑ e ∈ E \ H, DoublingMST.edgeCost d e + (1 - 1 / lam) * ∑ j, ∑ e ∈ E ∩ H, t j e
      - 2 * ∑ e ∈ E, (DoublingMST.edgeCost d e - U e)
      ≤ ∑ j, ∑ e ∈ E, t j e := by sorry

end MetricTSPSublinear
