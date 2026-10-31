-- Prove2me | Theorems.Thm_MinBuying_canonical_list_completion
-- name    : MinBuying.canonical_list_completion
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:42:58.035044+00:00
-- url     : https://prove2.me/theorems/67d6c43b-45e9-4d6e-9be2-46a1e1242d1f
-- title:
--   Finite canonical completion of a continuation list
-- statement:
--   Let L be a finite list of positive triangular parameters (a,v), with caps v>1 in strictly decreasing order. Start the continuation recursion at C∈[0,1], and suppose its final value exceeds one. Assume every positive uniform price t satisfies the relaxed bound
--
--   $$t\left[1-\frac{t}{t+C}\prod_{(a,v)\in L}\Pr_{\operatorname{Tri}(a,v)}(V<t)\right]\le1.$$
--
--   For every ε>0, there is a genuine canonical instance with at most |L| additional items, optimal uniform revenue at most one, and cap-pricing revenue at least the original final continuation minus ε. This is the constructive first-crossing step of the canonical reduction, including a finite terminal item.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, proof of Lemma 2, electronic companion ec8–ec11. Supporting constructive lemma.

import Definitions.Def_MinBuying_Triangular

namespace MinBuying

/-- Complete the first continuation crossing by a finite terminal item; the
recursive relaxed uniform constraint is the prefix estimate in Lemma 2. -/
theorem canonical_list_completion (L : List (ℝ × ℝ))
    (hpar : ∀ x ∈ L, 0 < x.1 ∧ 1 < x.2)
    (hdec : L.Pairwise (fun x y => y.2 < x.2))
    (C : ℝ) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hUP : ∀ t : ℝ, 0 < t →
      t * (1 - (t / (t + C)) *
        (L.map (fun x => triangularReject x.1 x.2 t)).prod) ≤ 1)
    (hfinal : 1 < L.foldl (fun S x => continuationStep x.1 x.2 S) C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : CanonicalInstance, J.count ≤ L.length ∧
      L.foldl (fun S x => continuationStep x.1 x.2 S) C - ε ≤ canonicalCapRevenue J ∧
      UPRevenue (canonicalLaw J) ≤ 1 := by
  sorry

end MinBuying
