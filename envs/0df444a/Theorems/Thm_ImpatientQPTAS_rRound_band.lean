-- Prove2me | Theorems.Thm_ImpatientQPTAS_rRound_band
-- name    : ImpatientQPTAS.rRound_band
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T21:01:43.66383+00:00
-- url     : https://prove2.me/theorems/33de1739-c37b-4864-8ccc-91aa27439543
-- title:
--   §2.2, p.9 — the rounded rewards lie in the band of Lemma 2.3
-- statement:
--   Let $\epsilon>0$ and let $r$ be non-negative rewards. The rounded reward $\tilde r_i$ of §2.2 satisfies
--   $$
--   0\le\tilde r_i\le r_i,\qquad \frac{r_i}{1+\epsilon}-\frac{\epsilon}{n}\,r_{\max}\le\tilde r_i .
--   $$
--
--   This connects the rounding the program uses to Lemma 2.3.
--
--   Differences from the source:
--   - reading: r̃_i is r_i rounded down to the nearest power of 1 + ε → r̃_i is r_i rounded down to the grid r_max·(1+ε)^(−j); reason: the page's rounding after normalizing r_max = 1; absolute powers would need a logarithm, and the bounds of Lemma 2.3 and the count of values are the same
--   - reading: the two bullets overlap at r_i = (ε/n)·r_max → r̃_i = 0 there; reason: both choices satisfy the bounds
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, §2.2, p.9

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes
import Definitions.Def_ImpatientQPTAS_Rounding

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, §2.2, p.9: the rounding `rRound` lies in the band of Lemma 2.3. For
non-negative rewards, `0 ≤ r̃_i ≤ r_i` and `r_i/(1+ε) − (ε/n)·r_max ≤ r̃_i`. -/
theorem rRound_band {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (i : Fin n) :
    0 ≤ rRound ε n (rmax r) (r i) ∧ rRound ε n (rmax r) (r i) ≤ r i ∧
      r i / (1 + ε) - ε / (n : ℝ) * rmax r ≤ rRound ε n (rmax r) (r i) := by sorry

end ImpatientQPTAS
