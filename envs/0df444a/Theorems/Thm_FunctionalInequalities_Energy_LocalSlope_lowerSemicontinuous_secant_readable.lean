-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_lowerSemicontinuous_secant_readable
-- name    : FunctionalInequalities.Energy.LocalSlope.lowerSemicontinuous_secant_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:51.432+00:00
-- url     : https://prove2.me/theorems/fd7d5e26-5f7d-4c26-af0b-4d2fd37844d8
-- title:
--   Lower Semicontinuity Of The Secant Supremum
-- statement:
--   This lemma establishes lower semicontinuity of each fixed-radius secant supremum.
--
--   Let $X$ be a metric space, let $f:X\to\mathbb R$ be continuous, and let $r\in\mathbb R$. Define `secant f r` at $x$ as the supremum, over points $y$ with $d(y,x)<r$, of the extended quotient
--
--   $$
--   \operatorname{ENNReal.ofReal}\!\left(\frac{d(f(y),f(x))}{d(y,x)}\right).
--   $$
--
--   Then the map $x\mapsto\operatorname{secant}(f,r)(x)$ is lower semicontinuous:
--
--   $$
--   \operatorname{LowerSemicontinuous}\bigl(\operatorname{secant}(f,r)\bigr).
--   $$
--
--   The Lean declaration is `lowerSemicontinuous_secant_readable`. The secant values are `ENNReal` values, so the conclusion allows the value $\top$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.LocalSlope`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lowerSemicontinuous_secant {f : X → ℝ} (hf : Continuous f) (r : ℝ) :
--       LowerSemicontinuous (secant f r)
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Density`](https://prove2.me/theorems/5367291c-d0c5-48f5-b722-92a892987587).
--
--   Definition modules: [`Energy/Euclidean/Slope/Recovery`](https://prove2.me/theorems/4d5469da-893c-48b4-9cb5-3ecfda5a30ce).
--
--   Next: [`exists_thickening_pairwise_disjoint`](https://prove2.me/theorems/b2a5cca9-524f-466c-8c07-05aff010b370).
--
--   [Source excerpt, lines 64–65](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L64-L65) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L63-L91 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Density`, declaration `FunctionalInequalities.Energy.LocalSlope.lowerSemicontinuous_secant`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density

variable {X : Type*} [MetricSpace X]

theorem FunctionalInequalities.Energy.LocalSlope.lowerSemicontinuous_secant_readable {f : X → ℝ} (hf : Continuous f) (r : ℝ) :
    LowerSemicontinuous (secant f r) := by sorry
