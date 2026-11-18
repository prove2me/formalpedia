-- Prove2me | Theorems.Thm_OWMR_con_retailer_budget
-- name    : OWMR.con_retailer_budget
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T12:51:33.643682+00:00
-- url     : https://prove2.me/theorems/51f51b23-aa8e-4be2-939f-1db554ac3255
-- title:
--   Retailer budgets of $\pi_{\rm con}$: immediate and batch retailers (Steps 5 and 6)
-- statement:
--   Let a network satisfy the standing assumptions, let $m\ge1$ with $mh\le H_i$ for all $i$ and $h\le p$, and let $c$ satisfy Definition 2. Write $k_i=\zeta_mK_i$, $G_i=J_i(k_i)$, $w_i=S_i-s_i$, $\psi(u)=\max(1-4u/3,0)^2/(8/3)$, and $c_i(f;K)$ for the long-run average cost of retailer $i$'s $(s_i,S_i)$ policy with setup cost $K$ and cost $f$ of the post-order position. For each retailer $i$:
--   1. (immediate retailer) if $i$ is not a batch retailer, then $s_i=S_i$, $S_i$ minimizes $F_i$, and $F_i(S_i)+K_i\le B_mG_i$;
--   2. (batch retailer) if $i$ is a batch retailer, then $s_i<S_i$ and
--   $$c_i\bigl(F_i;\tfrac73K_i\bigr)+c_i\bigl(h(S_i-\cdot)^+;0\bigr)+\min\Bigl(\tfrac38hw_i,\ (h+p)w_i\,c_i\bigl(\psi((S_i-\cdot)/w_i);0\bigr)\Bigr)+\tfrac38h\,\mathbb E D_i\le B_mG_i .$$
--   The left side of item 2 is the long-run cost charged to a batch retailer: its own costs with $7/3$ expected dispatches per order, the reserve it holds, the warehouse width cost, and its share of the trigger cost.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix C, Steps 5 and 6, Lemmas C.5 and C.6 with (C.24)-(C.28), pp. E.16-E.20; retailer choice in Definition 2 (i), p. 27.

import Definitions.Def_owmr_consolidation_policy

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem con_retailer_budget {n : ℕ} (N : Network n) (hN : N.Standing) (m : ℝ) (hm : 1 ≤ m)
    (hH : ∀ i, m * N.h ≤ N.H i) (hp : N.h ≤ N.p) (c : ConChoice n) (hc : IsConChoice N m c)
    (i : Fin n) :
    (c.batch i = false → c.s i = c.S i ∧ (∀ y, N.F i (c.S i) ≤ N.F i y) ∧
      ENNReal.ofReal (N.F i (c.S i) + N.K i)
        ≤ ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i)) ∧
    (c.batch i = true → c.s i < c.S i ∧
      ssAvgCost (N.marginal i) (N.F i) (7 / 3 * N.K i) (c.s i) (c.S i)
        + ssAvgCost (N.marginal i) (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i)
        + min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
            (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
              * ssAvgCost (N.marginal i)
                  (fun y => max (1 - 4 * ((c.S i - y) / (c.S i - c.s i)) / 3) 0 ^ 2 / (8 / 3)) 0
                  (c.s i) (c.S i))
        + ENNReal.ofReal (3 / 8 * N.h * ∫ x, (x : ℝ) ∂(N.marginal i))
      ≤ ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i)) := by sorry
end OWMR
