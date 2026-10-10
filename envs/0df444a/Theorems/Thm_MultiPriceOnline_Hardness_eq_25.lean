-- Prove2me | Theorems.Thm_MultiPriceOnline_Hardness_eq_25
-- name    : MultiPriceOnline.Hardness.eq_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:30.259876+00:00
-- url     : https://prove2.me/theorems/2da9f73a-9be6-467b-bda5-ab48ca01346a
-- title:
--   (25), p. 24 — OPT of the counterexample is Σⱼ r⁽ʲ⁾(βⱼn)k = Σⱼ (r⁽ʲ⁾ − r⁽ʲ⁻¹⁾)Bⱼnk, up to rounding
-- statement:
--   Let $m \ge 1$, let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set with booking limits $\alpha$, and let $B$ be the solution of Proposition 4. Consider the counterexample of §5 with $n$ items, inventory $k$, and any permutation $\pi$. For any $\pi$, the optimal value of the LP (5) is the revenue from serving every customer at the price of their phase:
--
--   $$\mathrm{OPT}(\mathcal S, \mathcal A_\pi) = k \sum_{g=0}^{n-1} r^{(\mathrm{phase}(g))}.$$
--
--   Moreover
--
--   $$\sum_{j=1}^m (r^{(j)} - r^{(j-1)}) B_j n k \;\le\; \mathrm{OPT}(\mathcal S, \mathcal A_\pi) \;\le\; \sum_{j=1}^m (r^{(j)} - r^{(j-1)}) B_j n k + k\,(r^{(m)} - r^{(1)}).$$
--
--   The left end is the paper's expression (25). The gap comes only from rounding the phase borders $(1 - B_j) n$ to integers.
--
--   In the proof of Theorem 3 this value is the denominator: the expected revenue of every online algorithm is compared with it.
--
--   **Formalization Note** The paper takes every $B_j n$ to be an integer (p. 23), and then $\mathrm{OPT} = \sum_j r^{(j)} (\beta_j n) k = \sum_j (r^{(j)} - r^{(j-1)}) B_j n k$ exactly. For a general $n$ the phase borders are $\lfloor (1 - B_j) n \rfloor$. Then the first equation is exact, and (25) holds up to the stated error, which is at most $k(r^{(m)} - r^{(1)})$ and does not grow with $n$. An exact version under the hypothesis "$B_j n \in \mathbb N$ for all $j$" was not posed: for irrational $B_j$ only $n = 0$ satisfies it.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 24, eq. (25) and the paragraph before it

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
import Definitions.Def_MultiPriceOnline_Hardness_Model
import Definitions.Def_MultiPriceOnline_Hardness_Instance

namespace MultiPriceOnline.Hardness
open Finset
theorem eq_25 {m : ℕ} {r α B : ℕ → ℝ} (hm : 1 ≤ m) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (hB : IsPhaseB m r α B) (n k : ℕ) (π : Equiv.Perm (Fin n)) :
    OPT k m r (hardInstance n k m B π) = (k : ℝ) * ∑ g : Fin n, r (phaseOf n m B g) ∧
    (∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * n * k)
      ≤ OPT k m r (hardInstance n k m B π) ∧
    OPT k m r (hardInstance n k m B π)
      ≤ (∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * n * k) + k * (r m - r 1) := by sorry
end MultiPriceOnline.Hardness
