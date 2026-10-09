-- Prove2me | Theorems.Thm_LimitedPriceChanges_LowerBound_lemma_2_corrected
-- name    : LimitedPriceChanges.LowerBound.lemma_2_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:09.492+00:00
-- url     : https://prove2.me/theorems/e560ba23-33e3-4a7d-840a-00b6d6f335ff
-- title:
--   Lemma 2 (corrected), p. 36 — interior Bernoulli KL bound
-- statement:
--   Let $z,z'\in[1/6,5/6]$ with $z\ge z'$, and let $p\in[1,6]$. If $pz\le11/6$, the two Bernoulli demand laws obey
--   $$D_{\mathrm{KL}}(P_z(\cdot\mid p)\|P_{z'}(\cdot\mid p))\le108(z-z')^2.$$
--   This gives a quadratic information bound when the success probabilities stay away from zero.
--
--   **Formalization Note** The printed lemma omits $pz\le11/6$ and is false: at $p=6$, $z=1/3$, $z'=1/3-a$, its KL divergence is $-\log(1-3a)$, of order $a$, while the printed right side is $108a^2$. The added condition keeps both Bernoulli probabilities in the interior.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 36, Lemma 2; p. 37, (54)–(55)

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL

namespace LimitedPriceChanges.LowerBound

/-- Lemma 2, p. 36, corrected with an interior-probability condition. -/
theorem lemma_2_corrected (z z' p : ℝ)
    (hz : z ∈ Set.Icc (1 / 6 : ℝ) (5 / 6 : ℝ))
    (hz' : z' ∈ Set.Icc (1 / 6 : ℝ) (5 / 6 : ℝ))
    (hzz' : z' ≤ z) (hp : p ∈ Set.Icc (1 : ℝ) 6)
    (hinterior : p * z ≤ 11 / 6) :
    klBer (nu p z) (nu p z') ≤ 108 * (z - z') ^ 2 := by sorry

end LimitedPriceChanges.LowerBound
