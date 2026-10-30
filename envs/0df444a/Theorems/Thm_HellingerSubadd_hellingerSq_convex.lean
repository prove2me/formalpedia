-- Prove2me | Theorems.Thm_HellingerSubadd_hellingerSq_convex
-- name    : HellingerSubadd.hellingerSq_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:51:06.543377+00:00
-- url     : https://prove2.me/theorems/c2827f33-940f-4aed-b586-8e185c7e0712
-- title:
--   Convexity of squared Hellinger distance
-- statement:
--   Let $\mu_1,\mu_2,\nu_1,\nu_2$ be probability measures on a measurable space and $t\in[0,1]$. Then
--
--   $$
--   D^2_{\mathrm H}\bigl((1-t)\mu_1+t\mu_2,\ (1-t)\nu_1+t\nu_2\bigr)\le(1-t)\,D^2_{\mathrm H}(\mu_1,\nu_1)+t\,D^2_{\mathrm H}(\mu_2,\nu_2).
--   $$
--
--   The proof of Lemma A.13 uses the instances with one argument fixed, $D^2_{\mathrm H}(Q^{(i)},P^{(i)}_\lambda)\le(1-\lambda)D^2_{\mathrm H}(Q^{(i)},P^{(i)})+\lambda D^2_{\mathrm H}(Q^{(i)},Q^{(i)})$ in Term I, and the analogous bound for $D^2_{\mathrm H}(P^{(i)},P^{(i)}_\lambda)$ in Term II.
--
--   Differences from the source:
--   - reading: "convexity of squared Hellinger distance" → joint convexity on pairs of probability measures; reason: the standard meaning for an f-divergence; both uses on p. 74 are instances (one argument fixed), so the reading is not weaker than either
--   - encoding: convex combinations (1−t)μ₁ + tμ₂ and real weights → ENNReal.ofReal (1 − t) • μ₁ + ENNReal.ofReal t • μ₂, values in ℝ≥0∞; reason: for t ∈ [0, 1] the weights are exactly 1 − t and t
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, proof of Lemma A.13, p. 74 (unnumbered, "by convexity of squared Hellinger distance", Terms I and II)

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq

open MeasureTheory
open scoped ENNReal

namespace HellingerSubadd

/-- **Convexity of squared Hellinger distance.**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, proof of Lemma A.13, p. 74 (unnumbered): "Moreover, by convexity of squared
Hellinger distance, D²_H(Q^(i)(· | x_{1:i−1}), P^(i)_λ(· | x_{1:i−1})) ≤
(1 − λ)D²_H(Q^(i)(· | x_{1:i−1}), P^(i)(· | x_{1:i−1})) + λD²_H(Q^(i)(· | x_{1:i−1}), Q^(i)(· | x_{1:i−1}))";
used again in Term II ("where the last inequality uses convexity of squared Hellinger distance").

For probability measures `μ₁, μ₂, ν₁, ν₂` and `t ∈ [0, 1]`,
`D²_H((1−t)μ₁ + tμ₂, (1−t)ν₁ + tν₂) ≤ (1−t) D²_H(μ₁, ν₁) + t D²_H(μ₂, ν₂)`.

**Formalization Note.** "Convexity" is read as joint convexity on pairs of probability measures,
the standard meaning for an f-divergence; both uses on p. 74 are the instances `μ₁ = μ₂` (first
argument fixed). Weights enter through `ENNReal.ofReal`; values in `ℝ≥0∞`. -/
theorem hellingerSq_convex {α : Type*} [MeasurableSpace α] (μ₁ μ₂ ν₁ ν₂ : Measure α)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    hellingerSq (ENNReal.ofReal (1 - t) • μ₁ + ENNReal.ofReal t • μ₂)
        (ENNReal.ofReal (1 - t) • ν₁ + ENNReal.ofReal t • ν₂)
      ≤ ENNReal.ofReal (1 - t) * hellingerSq μ₁ ν₁
          + ENNReal.ofReal t * hellingerSq μ₂ ν₂ := by sorry

end HellingerSubadd
