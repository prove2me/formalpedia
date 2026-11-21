-- Prove2me | Theorems.Thm_MasulloRH_rational_strip_weight_translation_ratio
-- name    : MasulloRH.rational_strip_weight_translation_ratio
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:26:58.054159+00:00
-- url     : https://prove2.me/theorems/1fe9b1f2-f059-4b81-b89f-e7e49c9758d6
-- title:
--   Translation bound for the rational logarithmic strip weight
-- statement:
--   For nonnegative b and p, the ratio of the rational logarithmic strip weights at x and x+t is bounded uniformly in x by (2(1+t²))^(p/2) exp(b|t|). This is the weight comparison used under translation in the shearing argument. It follows by keeping the constant term in the polynomial weight.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen draft, p. 421, weight comparison in the proof of Lemma 9.3.1.5 leading to (9.3.1.7), specialized to the rational logarithmic strip weight in the calculation (10.4.2.27)–(10.4.2.28), p. 464. The displayed constant is an explicit bound from the weight calculation.

import Definitions.Def_MasulloRH_WeightedStripJetSpace

open MasulloRH

theorem MasulloRH.rational_strip_weight_translation_ratio (b p : ℝ) (hb : 0 ≤ b) (hp : 0 ≤ p) (x t : ℝ) :
    rationalStripWeight b p x / rationalStripWeight b p (x+t) ≤
      (2*(1+t^2)) ^ (p/2) * Real.exp (b*|t|) := by sorry
