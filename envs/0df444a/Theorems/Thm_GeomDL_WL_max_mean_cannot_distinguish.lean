-- Prove2me | Theorems.Thm_GeomDL_WL_max_mean_cannot_distinguish
-- name    : GeomDL.WL.max_mean_cannot_distinguish
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:58.652877+00:00
-- url     : https://prove2.me/theorems/66954e79-1e69-4684-916a-faa8e536170c
-- title:
--   Side-note p. 120 — max and mean cannot distinguish {{a, b}} from {{a, a, b, b}}
-- statement:
--   Let $a, b \in \mathbb R^d$ be any two feature vectors. The neighbour multisets $\{\!\{a, b\}\!\}$ and $\{\!\{a, a, b, b\}\!\}$ are different, but the maximisation and averaging aggregators take the same value on both:
--   $$
--   \max\{\!\{a, b\}\!\} = \max\{\!\{a, a, b, b\}\!\}, \qquad \tfrac12 (a + b) = \tfrac14 (a + a + b + b).
--   $$
--
--   Hence a GNN whose aggregator is a maximum or a mean cannot separate two nodes whose neighbourhoods differ only by such a duplication, which is why those aggregators fall short of the WL test.
--
--   **Formalization Note** The maximum of vectors is coordinatewise, valued in $\mathbb R^d$ extended by a bottom element for the empty multiset; the mean is $|S|^{-1} \sum_{x \in S} x$.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), Ch. 7, side-note p. 120

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_GeomDL_WL_Defs

namespace GeomDL.WL

/-- Side-note p. 120: maximisation and averaging cannot distinguish the neighbour multisets
`{{a, b}}` and `{{a, a, b, b}}`: the two multisets differ, but their coordinatewise maxima and
their means coincide, for all feature vectors `a, b ∈ ℝ^d`. -/
theorem max_mean_cannot_distinguish {d : ℕ} (a b : Fin d → ℝ) :
    ({a, b} : Multiset (Fin d → ℝ)) ≠ {a, a, b, b} ∧
      maxAgg ({a, b} : Multiset (Fin d → ℝ)) = maxAgg {a, a, b, b} ∧
      meanAgg ({a, b} : Multiset (Fin d → ℝ)) = meanAgg {a, a, b, b} := by sorry

end GeomDL.WL
