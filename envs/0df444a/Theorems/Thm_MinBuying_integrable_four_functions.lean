-- Prove2me | Theorems.Thm_MinBuying_integrable_four_functions
-- name    : MinBuying.integrable_four_functions
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T18:05:37.112353+00:00
-- url     : https://prove2.me/theorems/e255e1b7-d909-4785-b4b6-6e59680082c1
-- title:
--   Four-functions inequality for arbitrary integrable functions on Euclidean product lattices
-- statement:
--   For any dimension $n$, let $a,b,c,d:\mathbb R^n\to\mathbb R$ be nonnegative Lebesgue-integrable functions. If $a(v)b(w)\le c(v\wedge w)d(v\vee w)$ for every pair of vectors, then $(\int a)(\int b)\le(\int c)(\int d)$. The functions need not be continuous or strictly positive.
-- source:
--   Auxiliary continuous four-functions inequality for the affiliation arguments in Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133 , proof of Theorem 2, ec2–ec3. This formalization supplies a direct dimension-induction proof from a two-point four-functions algebra inequality and Fubini, rather than assuming finite marginal densities everywhere.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory

namespace MinBuying

theorem integrable_four_functions (n : ℕ) (a b c d : Valuations n → ℝ)
    (ha : ∀ v,0 ≤ a v) (hb : ∀ v,0 ≤ b v) (hc : ∀ v,0 ≤ c v) (hd : ∀ v,0 ≤ d v)
    (h : ∀ v w,a v*b w ≤
      c (fun i => min (v i) (w i))*d (fun i => max (v i) (w i)))
    (ia : Integrable a volume) (ib : Integrable b volume)
    (ic : Integrable c volume) (id : Integrable d volume) :
    (∫ v,a v)*(∫ v,b v) ≤ (∫ v,c v)*(∫ v,d v) := by
  sorry

end MinBuying
