-- Prove2me | Theorems.Thm_LeightonRao_BadExample_max_flow_le
-- name    : LeightonRao.BadExample.max_flow_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:25:59.803002+00:00
-- url     : https://prove2.me/theorems/1a515843-4399-4a9b-9856-7210ef17f984
-- title:
--   §2.1, pp. 794–795 — the uniform max-flow on a 3-regular unit-capacity graph is f ≤ 6/((n − 1)(⌊log n⌋ − 2))
-- statement:
--   Let $G$ be a 3-regular graph on $n\ge 8$ nodes with unit edge capacities, and write $\log$ for $\log_2$. The max-flow $f$ of the uniform multicommodity flow problem on $G$ satisfies
--   $$f\ \le\ \frac{3n}{\binom n2\bigl(\lfloor\log n\rfloor-2\bigr)}\ =\ \frac{6}{(n-1)\bigl(\lfloor\log n\rfloor-2\bigr)} .$$
--
--   Together with the lower bound $\mathcal S\ge c/(n-1)$ on the min-cut of an expander, this gives the $\Theta(\log n)$ gap of the example.
--
--   **Formalization Note** The max-flow is the supremum of the feasible concurrent fractions. The paper's $\log n-2$ is stated with the floor $\lfloor\log n\rfloor-2$ (printed slip; the argument proves the floor version), and $n\ge 8$ makes it at least $1$. The text just before the argument says "at most $6/(n-1)(\log n-1)$"; the display, which is what is formalized, has $\log n-2$.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 794–795, §2.1, final display, first two lines

import Mathlib
import Definitions.Def_LeightonRao_BadExample_Setting

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.BadExample

/-- §2.1, pp. 794–795: the uniform max-flow of a 3-regular unit-capacity network with
`n ≥ 8` nodes is at most `3n/((n choose 2)(⌊log₂ n⌋ − 2)) = 6/((n − 1)(⌊log₂ n⌋ − 2))`. -/
theorem max_flow_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3)
    (hn : 8 ≤ Fintype.card V) :
    maxFlow (unitNetwork G) uniformDemand ≤
      6 / (((Fintype.card V : ℝ) - 1) * ((Nat.log 2 (Fintype.card V) : ℝ) - 2)) := by sorry

end LeightonRao.BadExample
