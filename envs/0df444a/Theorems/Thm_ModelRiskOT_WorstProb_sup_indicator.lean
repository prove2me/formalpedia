-- Prove2me | Theorems.Thm_ModelRiskOT_WorstProb_sup_indicator
-- name    : ModelRiskOT.WorstProb.sup_indicator
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:04:03.216087+00:00
-- url     : https://prove2.me/theorems/74f3e723-9098-4c33-8119-75cf96d309d0
-- title:
--   §2.4, pp. 8–9 — $\sup_{y \in S}\{1_A(y) - \lambda c(x,y)\} = (1 - \lambda c(x,A))^+$
-- statement:
--   Let $S$ be a Polish space, let $c : S \times S \to \mathbb R_+$ satisfy (A1), let $A \subseteq S$ be nonempty and closed, $\lambda \ge 0$ and $x \in S$. With $c(x,A) = \inf\{c(x,y) : y \in A\}$,
--   $$\sup_{y \in S}\{1_A(y) - \lambda c(x,y)\} = \big(1 - \lambda c(x,A)\big)^+ .$$
--
--   This identifies the function $\varphi_\lambda(x) = \sup_y\{f(y) - \lambda c(x,y)\}$ of the dual problem when $f = 1_A$; with it, the dual of the worst-case probability problem becomes the univariate problem (13).
--
--   **Formalization Note** The supremum is a real supremum (`iSup` in $\mathbb R$); the family is bounded above by $1$ and nonempty, so it is the true supremum. Only $c \ge 0$ and $c(x,x) = 0$ from (A1) are used.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, pp. 8–9, §2.4, display after (12)

import Mathlib
import Definitions.Def_ModelRiskOT_WorstProb_WorstCaseProb

open MeasureTheory
open scoped ENNReal

namespace ModelRiskOT.WorstProb

/-- §2.4, pp. 8–9: for `λ ≥ 0` and a nonempty closed set `A` in a Polish space,
`sup_{y ∈ S} {1_A(y) − λ c(x, y)} = (1 − λ c(x, A))⁺`, where `c(x, A) = inf_{y ∈ A} c(x, y)`. -/
theorem sup_indicator {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (hc : ModelRiskOT.Duality.AssumptionA1 c)
    (A : Set S) (hA : IsClosed A) (hAne : A.Nonempty) (lam : ℝ) (hlam : 0 ≤ lam) (x : S) :
    ⨆ y : S, (A.indicator (fun _ => (1 : ℝ)) y - lam * c x y) =
      max (1 - lam * costToSet c A x) 0 := by sorry

end ModelRiskOT.WorstProb
