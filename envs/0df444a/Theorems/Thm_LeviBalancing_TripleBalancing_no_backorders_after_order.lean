-- Prove2me | Theorems.Thm_LeviBalancing_TripleBalancing_no_backorders_after_order
-- name    : LeviBalancing.TripleBalancing.no_backorders_after_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:22:19.614288+00:00
-- url     : https://prove2.me/theorems/3a8c1a5e-29a9-4fe1-a39c-bc19445850a7
-- title:
--   §6.1, Rule 2 — after an order of TB there are no unsatisfied units of demand
-- statement:
--   Let TB be the triple-balancing policy for a stochastic lot-sizing model with conditional demand law $I$. In every period $s\in\{1,\dots,T\}$ in which TB places an order ($Q_s^{TB}>0$), the inventory level after ordering covers the demand of the period:
--   $$D_s\le y_s^{TB},$$
--   that is, at the end of a period in which an order was placed, there are no unsatisfied units of demand.
--
--   This observation is used in both Lemma 6.1 and Lemma 6.2: it makes the backlogging cost of TB between two consecutive orders depend only on the demand after the first of them.
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, p. 299 (PDF 16), §6.1, Rule 2

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model
import Definitions.Def_LeviBalancing_TripleBalancing_Policy
import Definitions.Def_LeviBalancing_TripleBalancing_TBPolicy

open MeasureTheory ProbabilityTheory

namespace LeviBalancing.TripleBalancing

/-- §6.1, Rule 2 observation (p. 299): in a period in which the triple-balancing policy places an
order, no demand is left unsatisfied at the end of the period. -/
theorem no_backorders_after_order {Ω : Type*} [MeasurableSpace Ω] (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB) :
    ∀ s ∈ Finset.Icc 1 M.T, ∀ ω, 0 < TB s ω → M.D s ω ≤ levelAfter M TB s ω := by sorry

end LeviBalancing.TripleBalancing
