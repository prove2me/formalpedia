-- Prove2me | Theorems.Thm_LostSalesOrderUpTo_Asymptotic_lemma13
-- name    : LostSalesOrderUpTo.Asymptotic.lemma13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:49:18.633981+00:00
-- url     : https://prove2.me/theorems/c01650da-503f-41b2-b1b5-392644ebd977
-- title:
--   Lemma 13 — backorder cost sandwich
-- statement:
--   For a lost-sales system with lead time $\tau$, holding rate $h>0$, lost-sales penalty $b>0$, and any order-up-to level $S\ge0$, let $C^{\mathcal L,S}(h,b)$ be its long-run average cost. Then
--
--   $$C^{\mathcal B,S}\!\left(h,\frac{b}{\tau+1}\right)\le C^{\mathcal L,S}(h,b)\le C^{\mathcal B,S}(h,b+\tau h).$$
--
--   The same level $S$ appears in both backorder bounds. The exact penalties are needed to compare the proposed policy with unrestricted optimal lost-sales cost.
--
--   **Formalization Note** Lost-sales cost is the limsup of expected Cesàro averages from the empty state, represented in $[0,\infty]$; backorder cost is finite and represented in $\mathbb R$.
-- source:
--   Huh, Janakiraman, Muckstadt & Rusmevichientong, Asymptotic Optimality of Order-up-to Policies in Lost Sales Inventory Systems, working paper, December 4, 2006 (preprint of Management Science 55(3), 2009, DOI 10.1287/mnsc.1080.0945), p. 15, Lemma 13

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

/-- Lemma 13: the two explicit backorder penalties bracket lost-sales cost. -/
theorem lemma13 (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (S : ℝ≥0) :
    ENNReal.ofReal (backorderCost (leadTimeLaw P c.L) c.h
        (c.p / ((c.L : ℝ) + 1)) S) ≤
      CappedBaseStock.baseStockCost P c S ∧
    CappedBaseStock.baseStockCost P c S ≤
      ENNReal.ofReal (backorderCost (leadTimeLaw P c.L) c.h
        (c.p + (c.L : ℝ) * c.h) S) := by sorry

end LostSalesOrderUpTo.Asymptotic
