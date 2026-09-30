-- Prove2me | Theorems.Thm_OptimalBAI_TrackStop_lambert_inversion
-- name    : OptimalBAI.TrackStop.lambert_inversion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:16:50.5633+00:00
-- url     : https://prove2.me/theorems/2e18cef1-efba-4ef5-9c3c-58488ed78a49
-- title:
--   Lemma 18 — an explicit solution of $c_1x\ge\log(c_2x^\alpha)$
-- statement:
--   Let $\alpha\in[1,e/2]$ and let $c_1,c_2>0$ be constants with $c_2/c_1^\alpha>1$. If
--   $$x=\frac{\alpha}{c_1}\left[\log\left(\frac{c_2e}{c_1^\alpha}\right)+\log\log\left(\frac{c_2}{c_1^\alpha}\right)\right]$$
--   is positive, then
--   $$c_1x\ge\log\big(c_2x^\alpha\big).$$
--
--   The lemma inverts the inequality $c_1x\ge\log(c_2x^\alpha)$ up to the constant $\alpha$, as bounds on the Lambert $W$ function do; it converts the threshold $\log(r(t)/\delta)$ into an explicit time after which Chernoff's rule has stopped.
--
--   **Formalization Note** The paper states the lemma for all $c_1,c_2>0$. Two hypotheses are added so that the printed expressions are defined: $c_2/c_1^\alpha>1$ (otherwise $\log\log(c_2/c_1^\alpha)$ is the logarithm of a non-positive number) and $x>0$ (otherwise $x^\alpha$ is undefined; $x\le0$ happens for $c_2/c_1^\alpha$ slightly above $1$). Every use in the paper has $c_2/c_1^\alpha\to\infty$.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 27, Lemma 18

import Mathlib

namespace OptimalBAI.TrackStop

/-- Lemma 18 (Garivier–Kaufmann, arXiv:1602.04589v2, p. 27). For `α ∈ [1, e/2]` and constants
`c₁, c₂ > 0`, the number
`x = (α/c₁) [log(c₂ e / c₁^α) + log log(c₂ / c₁^α)]` satisfies `c₁ x ≥ log(c₂ x^α)`.
Two hypotheses are added so that the printed expressions are defined: `c₂ / c₁^α > 1` (so that
`log log(c₂/c₁^α)` is the logarithm of a positive number) and `x > 0` (so that `x^α` is defined). -/
theorem lambert_inversion (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) (Real.exp 1 / 2))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hy : c₁ ^ α < c₂)
    (x : ℝ)
    (hx : x = α / c₁ * (Real.log (c₂ * Real.exp 1 / c₁ ^ α) + Real.log (Real.log (c₂ / c₁ ^ α))))
    (hx_pos : 0 < x) :
    Real.log (c₂ * x ^ α) ≤ c₁ * x := by sorry

end OptimalBAI.TrackStop
