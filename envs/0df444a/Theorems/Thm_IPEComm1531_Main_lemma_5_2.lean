-- Prove2me | Theorems.Thm_IPEComm1531_Main_lemma_5_2
-- name    : IPEComm1531.Main.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:28.6472+00:00
-- url     : https://prove2.me/theorems/c09724a3-adca-4ebf-a090-15f17a5d64eb
-- title:
--   Lemma 5.2 — two dense sets of the cube contain points at distance $\sqrt{r\ln(1/(\alpha\beta))}$
-- statement:
--   For any nonempty $X,Z\subseteq\{0,1\}^r$ with densities $\alpha=|X|/2^r$ and $\beta=|Z|/2^r$ there are $x\in X$ and $z\in Z$ with
--   $$|x\oplus z|\le\sqrt{r\ln\frac1{\alpha\beta}} .$$
--
--   Here $\ln$ is the natural logarithm. This provides the close pair from which a $1$-input is built inside every large rectangle.
--
--   Differences from the source: none.
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, Lemma 5.2, p.11 (proof in Appendix C, p.19)

import Mathlib
import Definitions.Def_IPEComm1531_Main_Basic

namespace IPEComm1531.Main

/-- Lemma 5.2 (close points in two nonempty sets of the cube), p.11. -/
theorem lemma_5_2 (r : ℕ) (X Z : Finset (Bits r)) (hX : X.Nonempty) (hZ : Z.Nonempty) :
    ∃ x ∈ X, ∃ z ∈ Z,
      (distance x z : ℝ) ≤ Real.sqrt (r * Real.log (1 / (density X * density Z))) := by sorry

end IPEComm1531.Main
