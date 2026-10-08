-- Prove2me | Theorems.Thm_Menger27_Curves_order_eq_max_nBein
-- name    : Menger27.Curves.order_eq_max_nBein
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:14:51.334919+00:00
-- url     : https://prove2.me/theorems/21065562-39c9-488e-9637-841313abfff5
-- title:
--   Theorem — point order is the largest number of legs
-- statement:
--   Let $R$ be a compact connected regular metric curve, and let $p\in R$ have exact order $n$. Then $n$ arcs end at $p$ and are pairwise disjoint elsewhere, while no such collection of $n+1$ arcs exists:
--   $$\operatorname{HasNBein}(p,n)\quad\text{and}\quad\neg\operatorname{HasNBein}(p,n+1).$$
--
--   Thus the order of $p$ is the greatest number of legs of a topological $n$-leg with vertex $p$. **Formalization Note** “Exact order” includes the exclusion of all smaller orders. Each leg is an injective arc $[0,1]\to R$ starting at $p$; constant arcs cannot satisfy the definition. The conclusion joins the first and third sentences of the printed Theorem, using the nonexistence observation from pp. 97–98.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 98, Theorem, first and third sentences; upper bound on pp. 97–98

import Mathlib
import Definitions.Def_Menger27_Curves_Basic

namespace Menger27.Curves

/-- Theorem, p. 98: exact order is the greatest number of legs at a point. -/
theorem order_eq_max_nBein {X : Type*} [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X]
    (hcurve : IsRegularCurve X) (p : X) (n : ℕ) (horder : HasOrder p n) :
    HasNBein p n ∧ ¬ HasNBein p (n + 1) := by sorry

end Menger27.Curves
