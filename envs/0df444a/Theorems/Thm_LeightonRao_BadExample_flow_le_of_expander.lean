-- Prove2me | Theorems.Thm_LeightonRao_BadExample_flow_le_of_expander
-- name    : LeightonRao.BadExample.flow_le_of_expander
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:25:48.103211+00:00
-- url     : https://prove2.me/theorems/2bb37836-8e47-492a-b417-04244903e9a6
-- title:
--   §2.1, pp. 794–795 — on a 3-regular c-expander the uniform max-flow is f ≤ 6𝒮/(c(⌊log n⌋ − 2))
-- statement:
--   Let $G$ be a 3-regular graph on $n\ge 8$ nodes with unit edge capacities, and suppose that for a constant $c>0$
--   $$|\langle U,\bar U\rangle|\ \ge\ c\,\min\{|U|,|\bar U|\}\qquad\text{for all }U\subseteq V .$$
--   Write $\log$ for $\log_2$, and let $f$ and $\mathcal S$ be the max-flow and the min-cut of the uniform multicommodity flow problem on $G$. Then
--   $$f\ \le\ \frac{6\,\mathcal S}{c\,\bigl(\lfloor\log n\rfloor-2\bigr)} .$$
--
--   Since $\mathcal S$ is the min-cut and $f\le\mathcal S$ always holds, this shows that on bounded-degree expanders the max-flow is a $\Theta(\log n)$ factor smaller than the min-cut, so the $O(\log n)$ gap of Theorem 2 is tight.
--
--   **Formalization Note** The paper's display has $\log n-2$; the argument (a ball of radius $\lfloor\log n\rfloor-3$ in a 3-regular graph has fewer than $n/2$ nodes) proves the bound with $\lfloor\log n\rfloor-2$, which is what is stated: the same $\Theta(\log n)$, a different constant. The hypothesis $n\ge 8$ makes $\lfloor\log n\rfloor-2\ge 1$. Commodities are ordered pairs of demand $1/2$ (footnote 2, p. 791); the min-cut ranges over nonempty proper cuts; the max-flow is the supremum of feasible concurrent fractions.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 794–795, §2.1, final display (f ≤ 6𝒮/(c(log n − 2)))

import Mathlib
import Definitions.Def_LeightonRao_BadExample_Setting

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.BadExample

/-- §2.1 display, pp. 794–795: on a 3-regular `n`-node graph with unit capacities and
`|⟨U, Ū⟩| ≥ c min{|U|, |Ū|}` for all `U`, with `n ≥ 8`, the uniform max-flow satisfies
`f ≤ 6𝒮/(c(⌊log₂ n⌋ − 2))`. -/
theorem flow_le_of_expander {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3)
    (c : ℝ) (hc : 0 < c) (hexp : IsEdgeExpander G c)
    (hn : 8 ≤ Fintype.card V) :
    maxFlow (unitNetwork G) uniformDemand ≤
      6 * minCut (unitNetwork G) /
        (c * ((Nat.log 2 (Fintype.card V) : ℝ) - 2)) := by sorry

end LeightonRao.BadExample
