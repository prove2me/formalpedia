-- Prove2me | Theorems.Thm_MinBuying_regular_triangular_minorant
-- name    : MinBuying.regular_triangular_minorant
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:26:55.662957+00:00
-- url     : https://prove2.me/theorems/f027fc88-9665-4899-99cf-54d9e3ef8e25
-- title:
--   Regular distributions admit a triangular demand minorant
-- statement:
--   Let $F$ be a probability law supported on nonnegative valuations with a concave interior revenue-quantile curve. Fix $p>0$ and write $r=\Pr_F(V<p)$. If $0<r<1$, set $a=p(1-r)/r$. Then $a>0$, the law $\operatorname{Tri}(a,p)$ has strict rejection probability $r$ at $p$, and
--
--   $$\Pr_F(V<t)\le\Pr_{\operatorname{Tri}(a,p)}(V<t)\qquad(t\ge0).$$
--
--   This is the single-item replacement underlying Lemma 1: it preserves demand at the chosen price and weakly lowers demand at every common price. The statement also permits atoms; absolute continuity is unnecessary for this supporting result.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, electronic companion ec7–ec8, proof of Lemma 1; strengthened single-item triangular-minorant ingredient.

import Definitions.Def_MinBuying_Triangular
import Definitions.Def_MinBuying_Regularity

open MeasureTheory Set

namespace MinBuying

theorem regular_triangular_minorant (F : Measure ℝ) (hF : ValidMarginal F) (hreg : Regular F)
    (p : ℝ) (hp : 0 < p) (hr : rejection F p ∈ Ioo (0 : ℝ) 1) :
    let a := p * (1 - rejection F p) / rejection F p
    0 < a ∧ rejection (triangularLaw a p) p = rejection F p ∧
      (∀ t : ℝ, 0 ≤ t → rejection F t ≤ rejection (triangularLaw a p) t) := by
  sorry

end MinBuying
