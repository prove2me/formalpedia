-- Prove2me | Theorems.Thm_IntMul_HvdH_scaleFP_bound
-- name    : IntMul.HvdH.scaleFP_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:47:02.780552+00:00
-- url     : https://prove2.me/theorems/996a44d3-e59e-4fa0-a045-fa1a36d31062
-- title:
--   Fixed-point scaling error (Lemma 2.2): $\varepsilon(\tilde v)<2c\,\varepsilon(\tilde u)+3$
-- statement:
--   Let $p\ge0$, let $c\ge1$ be an integer, and let $u\in\mathbb C$ with $|u|\le 1/c$, so that $v:=cu$ lies in the unit disc. Let $\tilde u\in\mathbb C$ be any approximation of $u$, and let $\tilde v$ be the output of the scaling procedure `scaleFP` (Lemma 2.2: take $c\tilde u$ if it lies in the unit disc, otherwise renormalise by $b=\lceil2^p|c\tilde u|\rceil$ and round). Then $|\tilde v|\le1$, and the errors $\varepsilon(\tilde v)=2^p|\tilde v-v|$ and $\varepsilon(\tilde u)=2^p|\tilde u-u|$ satisfy
--   $$\varepsilon(\tilde v)<2c\,\varepsilon(\tilde u)+3 .$$
--   This is the error statement of Lemma 2.2 of Harvey–van der Hoeven, used for example in the final scaling step of an inverse FFT.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.2, Lemma 2.2 (error bound)

import Definitions.Def_IntMul_HvdH_FixedPoint

namespace IntMul.HvdH
theorem scaleFP_bound (p c : ℕ) (hc : 1 ≤ c) (u ũ : ℂ) (hu : ‖u‖ ≤ (c : ℝ)⁻¹) :
    ‖scaleFP p c ũ‖ ≤ 1 ∧
      (2 : ℝ) ^ p * ‖scaleFP p c ũ - c * u‖ < 2 * c * ((2 : ℝ) ^ p * ‖ũ - u‖) + 3 := by sorry
end IntMul.HvdH
