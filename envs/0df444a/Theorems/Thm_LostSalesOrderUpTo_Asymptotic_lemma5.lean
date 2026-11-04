-- Prove2me | Theorems.Thm_LostSalesOrderUpTo_Asymptotic_lemma5
-- name    : LostSalesOrderUpTo.Asymptotic.lemma5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:49:32.070623+00:00
-- url     : https://prove2.me/theorems/293efdb0-eae8-4ded-ab83-8e8df085020a
-- title:
--   Lemma 5 — comparison of backorder penalties
-- statement:
--   Let $\mathbf D$ have a nonnegative distribution with finite mean, let $h,b,\nu>0$, and put $S_b=S^{\mathcal B*}(h,b)$ and $S_{\nu b}=S^{\mathcal B*}(h,\nu b)$. Where both expected holding quantities are positive, the following chain bounds the relative change of optimal backorder costs:
--
--   $$\frac{1+\psi(S_{\nu b};h,\nu b)}{1+\nu^{-1}\psi(S_{\nu b};h,\nu b)}=\frac{C^{\mathcal B*}(h,\nu b)}{C^{\mathcal B,S_{\nu b}}(h,b)}\le\frac{C^{\mathcal B*}(h,\nu b)}{C^{\mathcal B*}(h,b)}\le\frac{C^{\mathcal B,S_b}(h,\nu b)}{C^{\mathcal B*}(h,b)}=\frac{1+\nu\psi(S_b;h,b)}{1+\psi(S_b;h,b)}.$$
--
--   Here $\psi(S;h,b)$ is expected shortage charge divided by expected holding charge. The right side is used in Theorem 15(a).
--
--   **Formalization Note** Positive holding expectations ensure that the displayed ratios have their mathematical meaning.
-- source:
--   Huh, Janakiraman, Muckstadt & Rusmevichientong, Asymptotic Optimality of Order-up-to Policies in Lost Sales Inventory Systems, working paper, December 4, 2006 (preprint of Management Science 55(3), 2009, DOI 10.1287/mnsc.1080.0945), p. 11, Lemma 5

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

/-- Lemma 5, with both holding-cost denominators explicitly positive. -/
theorem lemma5 (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h b ν : ℝ) (hh : 0 < h) (hb : 0 < b) (hν : 0 < ν)
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ)
    (hhold_b : 0 < expectedHolding μ (newsvendorLevel μ h b))
    (hhold_νb : 0 < expectedHolding μ (newsvendorLevel μ h (ν * b))) :
    (1 + shortageHoldingRatio μ h (ν * b) (newsvendorLevel μ h (ν * b))) /
        (1 + (1 / ν) * shortageHoldingRatio μ h (ν * b)
          (newsvendorLevel μ h (ν * b))) =
      backorderOptimalCost μ h (ν * b) /
        backorderCost μ h b (newsvendorLevel μ h (ν * b)) ∧
    backorderOptimalCost μ h (ν * b) /
        backorderCost μ h b (newsvendorLevel μ h (ν * b)) ≤
      backorderOptimalCost μ h (ν * b) / backorderOptimalCost μ h b ∧
    backorderOptimalCost μ h (ν * b) / backorderOptimalCost μ h b ≤
      backorderCost μ h (ν * b) (newsvendorLevel μ h b) /
        backorderOptimalCost μ h b ∧
    backorderCost μ h (ν * b) (newsvendorLevel μ h b) /
        backorderOptimalCost μ h b =
      (1 + ν * shortageHoldingRatio μ h b (newsvendorLevel μ h b)) /
        (1 + shortageHoldingRatio μ h b (newsvendorLevel μ h b)) := by sorry

end LostSalesOrderUpTo.Asymptotic
