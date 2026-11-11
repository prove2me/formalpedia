-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_claim_2_18
-- name    : ListHashFurstenberg.Main.claim_2_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:45.273716+00:00
-- url     : https://prove2.me/theorems/3f4be168-c9d5-4333-9916-f5a83e6edad7
-- title:
--   Claim 2.18 — $\lceil\log(1/2)/\log(1-x)\rceil\le 2/x$
-- statement:
--   For every real $x\in(0,1)$,
--
--   $$\left\lceil\frac{\log(1/2)}{\log(1-x)}\right\rceil\le\frac{2}{x}.$$
--
--   This bounds the number of random rotations needed in Lemma 2.16 to raise a direction density $x$ to $1/2$, as used in the proof of Corollary 2.17. The ratio of logarithms does not depend on their base.
--
--   Differences from the source:
--   - encoding: $\log$ with unspecified base → natural logarithm; reason: only the ratio of two logarithms occurs, which is independent of the base.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Claim 2.18, p.18 (the ceiling is printed; text extraction loses it)

import Mathlib

namespace ListHashFurstenberg.Main

/-- Claim 2.18, p.18 of Kumar–Mon, STOC 2027 submission #1578. For `x ∈ (0, 1)`,
`⌈log(1/2) / log(1 - x)⌉ ≤ 2 / x`. -/
theorem claim_2_18 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (⌈Real.log (1 / 2) / Real.log (1 - x)⌉ : ℝ) ≤ 2 / x := by sorry

end ListHashFurstenberg.Main
