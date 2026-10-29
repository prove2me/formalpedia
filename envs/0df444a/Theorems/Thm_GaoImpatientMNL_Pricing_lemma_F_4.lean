-- Prove2me | Theorems.Thm_GaoImpatientMNL_Pricing_lemma_F_4
-- name    : GaoImpatientMNL.Pricing.lemma_F_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:21:56.225365+00:00
-- url     : https://prove2.me/theorems/2c5d09ef-26ff-47c8-b1c1-b53198501846
-- title:
--   Lemma F.4 — Logarithmic ratio inequality
-- statement:
--   For real numbers $s,t>1$, if $\log(st)+1/t-s=0$, then
--   $$s\ge 2-\frac1t.$$
--   This is the logarithmic inequality used to compare consecutive ratios in the relaxation.
--
--   Differences from the source: none.
-- source:
--   Gao et al., DOI 10.1287/opre.2021.2127, Lemma F.4, PDF p.48, printed p.ec11, held source.pdf.

import Mathlib

namespace GaoImpatientMNL.Pricing

theorem lemma_F_4 (s t : ℝ) (hs : 1 < s) (ht : 1 < t)
    (h : Real.log (s * t) + 1 / t - s = 0) : 2 - 1 / t ≤ s := by sorry

end GaoImpatientMNL.Pricing
