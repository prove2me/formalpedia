-- Prove2me | Theorems.Thm_MinBuying_triangular_list_pruning
-- name    : MinBuying.triangular_list_pruning
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:48:23.038038+00:00
-- url     : https://prove2.me/theorems/600edb11-306a-49c2-9593-909f50ec5520
-- title:
--   Pruning and equal-cap aggregation of triangular continuation lists
-- statement:
--   Consider a finite list of positive triangular parameters with weakly decreasing caps. Suppose its continuation from zero exceeds one. There is a list with no more entries, strictly decreasing caps greater than one, and continuation at least as large. At each positive common price t, its rejection product is also at least as large:
--
--   $$\prod_{(a,v)\in L}\Pr_{\operatorname{Tri}(a,v)}(V<t)\le\prod_{(a,v)\in M}\Pr_{\operatorname{Tri}(a,v)}(V<t).$$
--
--   This algebraic preprocessing supplies the strict cap ordering and cap lower bound required for a canonical instance, while preserving the differentiated-revenue lower bound and every uniform-revenue upper bound.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, proof of Lemma 2, electronic companion ec8–ec11. Supporting ordered-list preprocessing.

import Definitions.Def_MinBuying_Triangular

namespace MinBuying

/-- Remove the caps at most one and merge adjacent equal-cap triangular
items without increasing uniform revenue or decreasing a cap continuation above one. -/
theorem triangular_list_pruning (L : List (ℝ × ℝ))
    (hpar : ∀ x ∈ L, 0 < x.1 ∧ 0 < x.2)
    (hdec : L.Pairwise (fun x y => y.2 ≤ x.2))
    (hfinal : 1 < L.foldl (fun S x => continuationStep x.1 x.2 S) 0) :
    ∃ M : List (ℝ × ℝ), M.length ≤ L.length ∧
      (∀ x ∈ M, 0 < x.1 ∧ 1 < x.2) ∧
      M.Pairwise (fun x y => y.2 < x.2) ∧
      L.foldl (fun S x => continuationStep x.1 x.2 S) 0 ≤
        M.foldl (fun S x => continuationStep x.1 x.2 S) 0 ∧
      (∀ t : ℝ, 0 < t →
        (L.map (fun x => triangularReject x.1 x.2 t)).prod ≤
          (M.map (fun x => triangularReject x.1 x.2 t)).prod) := by
  sorry

end MinBuying
