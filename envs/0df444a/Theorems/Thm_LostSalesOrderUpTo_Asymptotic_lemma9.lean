-- Prove2me | Theorems.Thm_LostSalesOrderUpTo_Asymptotic_lemma9
-- name    : LostSalesOrderUpTo.Asymptotic.lemma9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:14:07.606528+00:00
-- url     : https://prove2.me/theorems/d999f836-e6c7-4f3b-b733-69fffe7f253a
-- title:
--   Lemma 9 — pathwise lost-sales/backorder comparison
-- statement:
--   Start a lost-sales and a backorder system at the same empty state. Under the same order-up-to level $S\ge0$ and demand path, let $X_t^{\mathcal L,S}$ and $X_t^{\mathcal B,S}$ be their inventories just after delivery; let $\mathrm{LOST}_t^{\mathcal L,S}$ and $\mathrm{BACK}_t^{\mathcal B,S}$ be their period-$t$ shortages. For every $t\ge\tau+1$ in the paper's indexing,
--
--   $$X_t^{\mathcal B,S}\le X_t^{\mathcal L,S},\qquad \mathrm{BACK}_t^{\mathcal B,S}-\sum_{i=t-\tau}^{t-1}\mathrm{LOST}_i^{\mathcal L,S}\le\mathrm{LOST}_t^{\mathcal L,S}\le\mathrm{BACK}_t^{\mathcal B,S}.$$
--
--   This coupling compares the systems on each demand realization and underlies the long-run cost bounds.
--
--   **Formalization Note** The empty initial state is an instance of the paper's common starting-state condition.
-- source:
--   Huh, Janakiraman, Muckstadt & Rusmevichientong, Asymptotic Optimality of Order-up-to Policies in Lost Sales Inventory Systems, working paper, December 4, 2006 (preprint of Management Science 55(3), 2009, DOI 10.1287/mnsc.1080.0945), p. 14, Lemma 9

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Coupling

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

/-- Lemma 9, from the shared empty initial state. -/
theorem lemma9 (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) (ht : c.L ≤ t) :
    backorderInventory c S ω t ≤ (lostInventory c S ω t : ℝ) ∧
    backorderUnits c S ω t -
      ∑ i ∈ Finset.Ico (t - c.L) t, (lostUnits c S ω i : ℝ) ≤
      (lostUnits c S ω t : ℝ) ∧
    (lostUnits c S ω t : ℝ) ≤ backorderUnits c S ω t := by sorry

end LostSalesOrderUpTo.Asymptotic
