-- Prove2me | Theorems.Thm_OWMR_arb_supplier_shortage
-- name    : OWMR.arb_supplier_shortage
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T12:51:39.535618+00:00
-- url     : https://prove2.me/theorems/0b166dca-db29-46af-ab15-31536023da2d
-- title:
--   Lemma C.4: supplier cost, the stockout frequency $\le h/(h+p)$, and the shift $a_0$
-- statement:
--   Let $n>0$, let a network satisfy the standing assumptions, let $m\ge1$ and $h\le p$, and let $c$ satisfy the requirements of Definition 2 (`IsConChoice`). Then there is $a_0\ge0$ such that $s_0\le S_0$, $0\le s_0$, $J_0(g_mK_0)<\infty$, and
--   1. $c(f_{L_0};K_0,s_0,S_0)\le J_0(g_mK_0)+ha_0$;
--   2. $ha_0+\inf_yf_{L_0}(y)\le J_0(g_mK_0)$;
--   3. $c\bigl(y\mapsto\mathbb P(D^{(L_0)}>y);0,s_0,S_0\bigr)\le h/(h+p)$,
--
--   where $c(\cdot)$ is the long-run average cost of the supplier's $(s_0,S_0)$ policy on the aggregate demand. Item 3 bounds the long-run frequency of supplier stockouts over a lead time.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix C, Step 4, Lemma C.4 (i)-(iii) with (C.19)-(C.20), pp. E.14-E.16; supplier choice in Definition 2 (iv), p. 27.

import Definitions.Def_owmr_consolidation_policy

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem arb_supplier_shortage {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) (m : ℝ)
    (hm : 1 ≤ m) (hhp : N.h ≤ N.p) (c : ConChoice n) (hc : IsConChoice N m c) :
    ∃ a0 : ℝ, 0 ≤ a0 ∧ c.s0 ≤ c.S0 ∧ 0 ≤ c.s0 ∧ N.J0 (conG m * N.K0) ≠ ∞ ∧
      ssAvgCost N.aggregate N.fL0 N.K0 c.s0 c.S0
        ≤ N.J0 (conG m * N.K0) + ENNReal.ofReal (N.h * a0) ∧
      ENNReal.ofReal (N.h * a0 + ⨅ y, N.fL0 y) ≤ N.J0 (conG m * N.K0) ∧
      ssAvgCost N.aggregate (fun y => ((Measure.pi fun _ : Fin N.L0 => N.aggregate)
          {w | y < ∑ j, (w j : ℝ)}).toReal) 0 c.s0 c.S0
        ≤ ENNReal.ofReal (N.h / (N.h + N.p)) := by sorry
end OWMR
