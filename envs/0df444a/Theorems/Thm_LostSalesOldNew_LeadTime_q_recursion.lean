-- Prove2me | Theorems.Thm_LostSalesOldNew_LeadTime_q_recursion
-- name    : LostSalesOldNew.LeadTime.q_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:14.665759+00:00
-- url     : https://prove2.me/theorems/b1af3dd7-004f-44d1-b782-9a13011f1c68
-- title:
--   §2, p. 1257 — the one-period costs satisfy q^l(x^l) = γE[q^{l−1}(x_+^{l−1})]
-- statement:
--   Consider the lost-sales system of Zipkin (2008), §2, with cost data $c,\hat h,p \ge 0$, discount factor $\gamma\in[0,1)$, transformed holding cost $h = \hat h - \gamma c$, and i.i.d. demand with law $D$ on $[0,\infty)$ with finite mean. Recall $q^0(y) = cy + hE[[y-d]^+] + pE[[y-d]^-]$ and $q^l(x^l) = \gamma^l E[q^0(y_{+l})]$, where $y_{+l}$ is the stock on hand $l$ periods after the state $x^l = (x_0,\dots,x_l)$.
--
--   For every $l \ge 1$ and every $x^l \in \mathbb R^{l+1}$,
--   $$q^l(x^l) = \gamma\, E\bigl[q^{l-1}(x_+^{l-1})\bigr],$$
--   where $x_+^{l-1} = ([x_0-d]^+ + x_1, x_2, \dots, x_l)$ and the expectation is over the current period's demand $d \sim D$.
--
--   The recursion computes the transformed one-period cost $q(x,z) = q^L(x^L)$ one period at a time, and it is the identity that makes the $q$ terms cancel in the paper's derivation of the lead-time bound (6).
--
--   **Formalization Note.** The paper states the recursion for $l = 1,\dots,L$; it is stated here for every $l \ge 1$ (in Lean, `l + 1` for `l : ℕ`), which contains the paper's range. The state is `Fin (l + 2) → ℝ` and need not be nonnegative. Finite mean demand (`Integrable id D`) is assumed so that the Bochner integrals defining $q^0$ and $q^l$ are the paper's expectations.
-- source:
--   Zipkin, Old and New Methods for Lost-Sales Inventory Systems, Operations Research 56(5) (2008), §2, the recursion for q^l, p. 1257

import Mathlib
import Definitions.Def_LostSalesOldNew_LeadTime_Model

namespace LostSalesOldNew.LeadTime

open MeasureTheory

theorem q_recursion (K : Costs) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : LostSalesOldNew.StateReduction.IsDemand D) (hmean : Integrable (fun d : ℝ => d) D)
    (l : ℕ) (x : Fin (l + 2) → ℝ) :
    qL K D (l + 1) x = K.γ * ∫ d, qL K D l (LostSalesOldNew.StateReduction.shift x d) ∂D := by sorry

end LostSalesOldNew.LeadTime
