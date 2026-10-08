-- Prove2me | Theorems.Thm_LeightonRao_BadExample_min_cut_ge
-- name    : LeightonRao.BadExample.min_cut_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:32.125338+00:00
-- url     : https://prove2.me/theorems/1e910565-ea95-487b-b665-b2892d08eb0b
-- title:
--   §2.1, p. 794 — on a c-edge-expander with unit capacities the uniform min-cut is 𝒮 ≥ c/(n − 1)
-- statement:
--   Let $G$ be a graph on $n\ge 2$ nodes with unit edge capacities such that, for a constant $c>0$,
--   $|\langle U,\bar U\rangle|\ge c\min\{|U|,|\bar U|\}$ for every $U\subseteq V$. Then the min-cut of the uniform multicommodity flow problem on $G$ satisfies
--   $$\mathcal S=\min_{\emptyset\ne U\subsetneq V}\frac{|\langle U,\bar U\rangle|}{|U|\,|\bar U|}\ \ge\ \frac{c}{n-1}.$$
--
--   This is the lower bound on the min-cut in Leighton and Rao's example of a $\Theta(\log n)$ gap between max-flow and min-cut.
--
--   **Formalization Note** Regularity is not needed for this inequality and is not assumed. The minimum is over nonempty proper $U$ (see the setting).
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 794, §2.1, min-cut display

import Mathlib
import Definitions.Def_LeightonRao_BadExample_Setting

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.BadExample

/-- §2.1, p. 794: on a graph with `|⟨U, Ū⟩| ≥ c min{|U|, |Ū|}` for all `U`, the uniform
min-cut with unit capacities is at least `c/(n − 1)`. -/
theorem min_cut_ge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℝ) (hc : 0 < c) (hexp : IsEdgeExpander G c)
    (hn : 2 ≤ Fintype.card V) :
    c / ((Fintype.card V : ℝ) - 1) ≤ minCut (unitNetwork G) := by sorry

end LeightonRao.BadExample
