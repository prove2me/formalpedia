-- Prove2me | Theorems.Thm_LefebvreVariations_cesaro_mean_of_vanishing_function
-- name    : LefebvreVariations.cesaro_mean_of_vanishing_function
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:27:06.154+00:00
-- url     : https://prove2.me/theorems/f2ecfe8b-e219-4cce-ae6e-35128982bc5e
-- title:
--   Lefebvre's variations, No. 205 — on a theme by Attouch, Boţ and Nguyen: the Cesàro mean of a nonnegative function tending to zero at infinity tends to zero
-- statement:
--   Let $\delta\ge0$ and let $a:[\delta,\infty)\to[0,\infty)$ be locally integrable with $a(u)\to0$ as $u\to\infty$. Then
--   $$\lim_{s\to\infty}\frac1s\int_\delta^s a(u)\,du=0 .$$
--
--   This is the continuous Cesàro lemma: the running average of a nonnegative function that vanishes at infinity vanishes. It is the case $p=1$ of the weighted averages $s^{-p}\int_\delta^s u^{p-1}a(u)\,du$.
--
--   **Formalization Note** The statement is that of `TimeScaleAvg.lemma_4` with the hypothesis `p = 1` added (then `u ^ (p - 1) = 1`, with real powers). `ha_nonneg` and `ha` are as in the parent: `a` is nonnegative on `Set.Ici δ` and tends to `0` at `atTop`. The hypothesis `hint` says that `u ↦ u ^ (p - 1) * a u` is integrable on each `Set.Icc δ s` with `s ≥ δ`; `δ = 0` is allowed.
--
--   **Why this is a variation.** Variation of the open platform problem TimeScaleAvg.lemma_4 (weighted averages s^(-p) times the integral of u^(p-1) a(u) of a function a vanishing at infinity vanish). This is the case p=1, the plain Cesàro mean, in the parent's own hypotheses. It is the parent with those values substituted, hence a consequence of the parent (no formal import).
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: TimeScaleAvg.lemma_4 (platform, Open), Lemma 4 of Attouch, Bot and Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, p.28, as given in the parent's source field (not independently re-checked). The case p=1 is the elementary continuous Cesaro lemma, proved by splitting the integral at a point beyond which a < epsilon (argument checked by hand; no citation needed).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open Filter Topology MeasureTheory

/-- The case `p = 1` of `TimeScaleAvg.lemma_4`: the Cesàro mean `(1/s) ∫_δ^s a(u) du` of a nonnegative function
tending to `0` at infinity tends to `0`.
Source: elementary (the continuous Cesàro lemma); the parent is Lemma 4 of Attouch, Boţ and Nguyen, arXiv:2208.08260v3 (as quoted on the platform). -/
theorem cesaro_mean_of_vanishing_function {δ p : ℝ} (hδ : 0 ≤ δ) (hp : p = 1) {a : ℝ → ℝ}
    (ha_nonneg : ∀ s ∈ Set.Ici δ, 0 ≤ a s) (ha : Tendsto a atTop (𝓝 0))
    (hint : ∀ s ∈ Set.Ici δ, IntegrableOn (fun u => u ^ (p - 1) * a u) (Set.Icc δ s)) :
    Tendsto (fun s => (1 / s ^ p) * ∫ u in δ..s, u ^ (p - 1) * a u) atTop (𝓝 0) := by
  sorry

end LefebvreVariations
