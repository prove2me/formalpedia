-- Prove2me | Theorems.Thm_LostSalesRQ_operating_transform
-- name    : LostSalesRQ.operating_transform
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:33:20.819532+00:00
-- url     : https://prove2.me/theorems/b453ea4d-e095-4384-9e2f-d6b1c1a9d371
-- title:
--   Eq. (26): reduction of the general-setup optimum to the zero-setup optimum
-- statement:
--   Fix $\mu\ge0$, $a\ge0$ and $k\ge0$.
--
--   1. For every $\theta\in[0,1)$ with $b=\sqrt{2k\theta}\le a$,
--   $$\mathrm{OPT}_k(\mu,a)\ge b+(1-\theta)\,\mathrm{OPT}_0\Big(\mu,\frac{a-b}{1-\theta}\Big).$$
--   2. $\mathrm{OPT}_k(\mu,a)\ge\min\{a,\sqrt{2k}\}$ (the case $\theta=1$).
--
--   A fraction $\theta$ of holding cost and all setup costs pay for the service credit of Lemma J.1; the remaining costs form a zero-setup problem with an adjusted penalty.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 4.6.2, eq. (26) and the following paragraph (p. 22); Appendix J.1, eq. (J.2) (p. A22).

import Definitions.Def_LostSalesRQ_model

namespace LostSalesRQ

theorem operating_transform (μ a k : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k) :
    (∀ θ : ℝ, 0 ≤ θ → θ < 1 → Real.sqrt (2 * k * θ) ≤ a →
      ENNReal.ofReal (Real.sqrt (2 * k * θ)) +
          ENNReal.ofReal (1 - θ) * OPTk μ ((a - Real.sqrt (2 * k * θ)) / (1 - θ)) 0 ≤
        OPTk μ a k) ∧
    ENNReal.ofReal (min a (Real.sqrt (2 * k))) ≤ OPTk μ a k := by sorry

end LostSalesRQ
