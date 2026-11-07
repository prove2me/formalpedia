-- Prove2me | Theorems.Thm_MeanBudgetXC_lemma_3_6
-- name    : MeanBudgetXC.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:27.787948+00:00
-- url     : https://prove2.me/theorems/3d2d1f98-c1f4-4b55-9467-4ea36c43662c
-- title:
--   Lemma 3.6 — rounding above the objective threshold
-- statement:
--   Let $2\le d\le N$. Let $q\ge0$ be a pair array, with $T_i(q)$ the sum of its $d-1$ largest coordinates incident to $i$, and let $p$ satisfy (5):
--   $$T_i(q)\le p_i\le\deg_q(i)=\sum_{j\ne i}q_{ij}\quad(i\in[N]),\qquad P_{\mathrm{tot}}=\sum_ip_i.$$
--   If $(x,y)\in R_{N,d}$ and $J_{p,q}(x,y)>P_{\mathrm{tot}}/2$, then exactly $d$ coordinates of $x$ exceed $1/2$, and every remaining coordinate is strictly below $1/2$.
--
--   This places every point above the threshold in a strict rounding chamber, the setting of Lemma 3.7.
--
--   Differences from the source:
--   - encoding: The vertex set is $[N]$ → it is an arbitrary finite type $V$ with $N=|V|$; reason: every finite type is in bijection with $[N]$, so no instance changes
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Lemma 3.6, with the setting of display (5), p.13

import Mathlib
import Definitions.Def_MeanBudgetXC_topSum
import Definitions.Def_MeanBudgetXC_rltPolytope
import Definitions.Def_MeanBudgetXC_rltObjective

namespace MeanBudgetXC

/-- **Lemma 3.6** (Rounding above the objective threshold) (Chao–Gao–Qi–Wang, *A Sharp
Mean-Budget Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256
882d9c71…9e76, Section 3.4, p.13). Let `2 ≤ d ≤ N`, `q ≥ 0`, and let `p` satisfy (5):
`T_i(q) ≤ p_i ≤ deg_q(i) = ∑_{j ≠ i} q_ij` for every `i`; put `P_tot = ∑_i p_i`. If
`(x, y) ∈ R_{N,d}` and `J_{p,q}(x, y) > P_tot/2`, then exactly `d` coordinates of `x` exceed `1/2`
and every remaining coordinate is strictly below `1/2`.

**Formalization Note** The vertex set is a generic finite type `V` with `N = card V`; the range
`2 ≤ d ≤ N` is the paper's ("The following RLT vertex bound holds for 2 ≤ d ≤ N", p.13). -/
theorem lemma_3_6 {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd2 : 2 ≤ d)
    (hdN : d ≤ Fintype.card V) (p : V → ℝ) (q : Pair V → ℝ) (hq : ∀ e, 0 ≤ q e)
    (h5 : ∀ i, topSum d q i ≤ p i ∧ p i ≤ ∑ j, entry q i j)
    (xy : (V → ℝ) × (Pair V → ℝ)) (hxy : xy ∈ rltPolytope V d)
    (hJ : (∑ i, p i) / 2 < rltObjective p q xy) :
    (Finset.univ.filter fun i => 1 / 2 < xy.1 i).card = d ∧
      ∀ i, ¬ (1 / 2 < xy.1 i) → xy.1 i < 1 / 2 := by sorry

end MeanBudgetXC
