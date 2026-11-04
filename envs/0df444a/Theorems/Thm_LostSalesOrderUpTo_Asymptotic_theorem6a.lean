-- Prove2me | Theorems.Thm_LostSalesOrderUpTo_Asymptotic_theorem6a
-- name    : LostSalesOrderUpTo.Asymptotic.theorem6a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:49:38.004148+00:00
-- url     : https://prove2.me/theorems/2a2f1510-171e-4d36-ab9e-fddf4bd1a05e
-- title:
--   Theorem 6(a) — shortage/holding ratio vanishes
-- statement:
--   Let $\mathbf D$ have a nonconstant nonnegative distribution with finite mean and satisfy Assumption 1: its mean residual life obeys $m_{\mathbf D}(t)/t\to0$ as $t\to\infty$. For each penalty $b>0$, take the newsvendor level $S^{\mathcal B*}(h,b)$ at a fixed holding rate $h>0$. Then
--
--   $$\lim_{b\to\infty}\psi(S^{\mathcal B*}(h,b);h,b)=0.$$
--
--   Thus the expected shortage charge becomes negligible relative to the expected holding charge at large penalties. The statement includes bounded and atomic demand laws.
--
--   **Formalization Note** The nonconstant-law hypothesis makes the paper's shortage-to-holding ratio defined for all sufficiently large penalties. A point-mass law would otherwise use Lean's zero-over-zero value, which is not the printed ratio. The main asymptotic theorem includes point-mass demand through its multiplicative formulation.
-- source:
--   Huh, Janakiraman, Muckstadt & Rusmevichientong, Asymptotic Optimality of Order-up-to Policies in Lost Sales Inventory Systems, working paper, December 4, 2006 (preprint of Management Science 55(3), 2009, DOI 10.1287/mnsc.1080.0945), p. 11, Theorem 6(a)

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

/-- Theorem 6(a), including bounded and atomic demand laws. -/
theorem theorem6a (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 0 < h)
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ)
    (hnonconstant : ¬ ∃ d : ℝ≥0, μ = Measure.dirac d)
    (hassumption : AssumptionOne μ) :
    Tendsto (fun b : ℝ => shortageHoldingRatio μ h b (newsvendorLevel μ h b))
      atTop (nhds 0) := by sorry

end LostSalesOrderUpTo.Asymptotic
