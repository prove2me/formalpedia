-- Prove2me | Theorems.Thm_IPEComm1531_Main_lemma_3_4
-- name    : IPEComm1531.Main.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:18.237166+00:00
-- url     : https://prove2.me/theorems/594842a1-2d20-416c-a601-19ca812e00a4
-- title:
--   Lemma 3.4 — addresses with pairwise distance at least $r/5$ (for the map of Appendix C)
-- statement:
--   Let $w_\sigma\in\{0,1\}^r$ ($\sigma\in\{0,1\}^d$) be the deterministic address code of Appendix C. For every constant $C$ there is $N$ such that for all $r\ge N$ and all $d\le C\log_2 r$,
--   $$|w_\sigma\oplus w_{\sigma'}|\ge\frac r5\qquad\text{for all }\sigma\neq\sigma'\in\{0,1\}^d .$$
--
--   The separation makes the shifted strings $y\oplus w_\sigma$ far apart, so that at most one address can accept and random sampling can locate it.
--
--   Differences from the source:
--   - generalization: there exists a deterministic mapping with this property → the specific greedy map of Appendix C has this property; reason: the specific map witnesses the existence claim, and IPE is defined with it
--   - encoding: Fix d = O(log n) and r = Θ(n) → for every C there is N such that the claim holds for all r ≥ N and d ≤ C log₂ r; reason: unpacking of the asymptotic regime; r = Θ(n) only links r to n, which does not occur in the conclusion
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, Lemma 3.4, p.8 (proof in Appendix C, p.18)

import Mathlib
import Definitions.Def_IPEComm1531_Main_Addresses

namespace IPEComm1531.Main

/-- Lemma 3.4 (separated addresses), p.8, for the deterministic map of Appendix C. -/
theorem lemma_3_4 (C : ℝ) :
    ∃ N : ℕ, ∀ r d : ℕ, N ≤ r → (d : ℝ) ≤ C * Real.logb 2 r →
      ∀ σ σ' : Bits d, σ ≠ σ' →
        (r : ℝ) ≤ 5 * (distance (address r d σ) (address r d σ') : ℝ) := by sorry

end IPEComm1531.Main
