-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_eq_3_18_spanning_tree_bound
-- name    : KallMayerSLP.Bonferroni.eq_3_18_spanning_tree_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:50.308989+00:00
-- url     : https://prove2.me/theorems/6e191e4c-fe57-484a-a343-9dd768546ba3
-- title:
--   Spanning tree lower bound on the distribution function
-- statement:
--   Let $\xi:\Omega\to\mathbb R^r$, $r\ge1$, be a random vector on a probability space and $x\in\mathbb R^r$. For every spanning tree $T$ of the complete graph on $r$ vertices, with edge weights $(i,j)\mapsto\mathbb P(B_i(x)\cap B_j(x))$,
--   $$
--   1-S_1(x)+w(T)\le F(x).
--   $$
--   In particular this holds for an optimal solution $T^*(x)$ of the maximum spanning tree problem (3.17), which is the bound (3.18).
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
--   - generalization: the bound is displayed for an optimal solution $T^*(x)$ of (3.17) → the bound holds for every spanning tree $T$; reason: the book's argument on pp.290–291 treats an arbitrary spanning tree, and taking $T=T^*(x)$ gives (3.18)
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.17) and (3.18), p.291 (PDF 300)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_exceedanceEvent
import Definitions.Def_KallMayerSLP_Bonferroni_jointCDF
import Definitions.Def_KallMayerSLP_Bonferroni_treeWeight

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The spanning tree lower bound: `1 - S₁(x) + w(T) ≤ F(x)` for every spanning tree `T` of the
complete graph on `r` vertices with edge weights `(i, j) ↦ ℙ(B_i(x) ∩ B_j(x))`; in particular for an
optimal solution `T*(x)` of (3.17), which is (3.18).

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.17) and (3.18), p.291 (PDF 300).

**Formalization Note.** A spanning tree of the complete graph on `Fin r` is a `SimpleGraph (Fin r)`
which is a tree: it has all of `Fin r` as vertices, and every simple graph on `Fin r` is a subgraph
of the complete graph. -/
theorem eq_3_18_spanning_tree_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (ξ : Ω → Fin r → ℝ) (hξ : Measurable ξ) (x : Fin r → ℝ) (T : SimpleGraph (Fin r)) (hT : T.IsTree) :
    1 - binomialMoment μ (exceedanceEvent ξ x) 1 + treeWeight μ (exceedanceEvent ξ x) T ≤
      jointCDF μ ξ x := by sorry

end KallMayerSLP.Bonferroni
