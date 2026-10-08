-- Prove2me | Theorems.Thm_LostSalesOldNew_LeadTime_lead_time_monotone
-- name    : LostSalesOldNew.LeadTime.lead_time_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:23.835133+00:00
-- url     : https://prove2.me/theorems/e5333d3f-8f0d-4466-9c63-493d613ab9a5
-- title:
--   §5 and (6), p. 1259 — f*^{L−1}(x^{L−2}) ≤ q^{L−1}(x^{L−1}) + f*^L(x^{L−1}) and f*^L(x^{L−1}) ≥ γE[f*^{L−1}(x_+^{L−2})]
-- statement:
--   Consider two lost-sales systems as in Zipkin (2008), §2, identical except for the lead time: **system $L$** and **system $L-1$**, with $L \ge 2$. Both have cost data $c,\hat h,p \ge 0$, discount factor $\gamma\in[0,1)$, and i.i.d. demand with law $D$ on $[0,\infty)$ with finite mean. Let $f^{*L}$ and $f^{*L-1}$ be their infinite-horizon optimal discounted costs.
--
--   A state of system $L$ is $x^{L-1} = (x_0,\dots,x_{L-1}) \ge 0$; removing its most recent order gives $x^{L-2} = (x_0,\dots,x_{L-2})$, a state of system $L-1$. Let $q^{L-1}(x^{L-1})$ be the one-period cost of §2, and let $x_+^{L-2} = ([x_0-d]^+ + x_1, x_2, \dots, x_{L-1})$ be the first $L-1$ components of the next state of system $L$ under demand $d$. Then:
--
--   1. the cost of system $L-1$ is at most the cost of system $L$ plus the one extra period cost that system $L-1$ incurs:
--   $$f^{*L-1}(x^{L-2}) \le q^{L-1}(x^{L-1}) + f^{*L}(x^{L-1});$$
--   2. inequality (6) holds:
--   $$f^{*L}(x^{L-1}) \ge \gamma\, E\bigl[f^{*L-1}(x_+^{L-2})\bigr].$$
--
--   The first inequality makes formal, in the discounted case, the paper's claim that the optimal cost is nondecreasing in the lead time: the two systems have state spaces of different dimension, and the comparison is at matching states. The second inequality is the lower bound on system $L$ computed from the solution of system $L-1$, used for the numerical bounds of the paper.
--
--   **Formalization Note.** In Lean the lead times are $n = L-1 \ge 1$ and $n+1$, avoiding natural-number subtraction; $x^{L-1}$ is `x : Fin (n + 1) → ℝ`, $x^{L-2}$ is `Fin.init x`, and $x_+^{L-2}$ is `shift x d`. Optimal costs take values in $[0,\infty]$, so the first inequality is kept in the paper's additive form rather than the "turned around" form with subtraction. The optimal cost is the limit of the finite-horizon costs of (2). The cost signs, $\gamma<1$ (both part of the paper's setting), finite mean demand and $x \ge 0$ are hypotheses.
-- source:
--   Zipkin, Old and New Methods for Lost-Sales Inventory Systems, Operations Research 56(5) (2008), §5 Monotonicity, p. 1259, the first display and (6)

import Mathlib
import Definitions.Def_LostSalesOldNew_LeadTime_Model

namespace LostSalesOldNew.LeadTime

open MeasureTheory

theorem lead_time_monotone (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : LostSalesOldNew.StateReduction.IsDemand D) (hmean : Integrable (fun d : ℝ => d) D)
    (n : ℕ) (hn : 1 ≤ n) (x : Fin (n + 1) → ℝ) (hx : ∀ i, 0 ≤ x i) :
    fStar K D n (Fin.init x) ≤ ENNReal.ofReal (qL K D n x) + fStar K D (n + 1) x ∧
    ENNReal.ofReal K.γ * ∫⁻ d, fStar K D n (LostSalesOldNew.StateReduction.shift x d) ∂D ≤ fStar K D (n + 1) x := by sorry

end LostSalesOldNew.LeadTime
