-- Prove2me | Theorems.Thm_MinBuying_continuous_dominates_step
-- name    : MinBuying.continuous_dominates_step
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:22:22.618177+00:00
-- url     : https://prove2.me/theorems/6e243305-6cc4-45af-8fd4-df367bdfaf05
-- title:
--   Lemma 3 proof: continuous evolution dominates one discrete step
-- statement:
--   For $0\le y\le x<1$ and initial continuation $z\ge1$, let $a=\exp(A(x)-A(y))-1$. Then $(a+z)/(1+xa)$ is at most the value at $x$ of the continuous benchmark flow initialized at $z$ at $y$.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . PDF pp.40–41/ec13–ec14, proof of Lemma 3.

import Definitions.Def_MinBuying_Analytic

open Set

namespace MinBuying

theorem continuous_dominates_step (y z x : ℝ)
    (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x < 1) (hz : 1 ≤ z) :
    let a := Real.exp (canonicalBudget x - canonicalBudget y) - 1
    (a + z) / (1 + x * a) ≤ benchmarkFlow y z x := by
  sorry

end MinBuying
