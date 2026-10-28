-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
-- name    : LevyStochCalc.Brownian.BrownianMotion.hasLaw_eval_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:53.714993+00:00
-- url     : https://prove2.me/theorems/1fb6389e-a58c-4dab-9daf-eb1e551698b4
-- title:
--   Brownian Motion Marginal Law
-- statement:
--   This is a marginal-law statement for a real Brownian motion.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space, let $W$ be a `BrownianMotion` under $P$, and let $t\in[0,\infty)$ be represented as an `NNReal`. Then the random variable $\omega\mapsto W_t(\omega)$ has the centered Gaussian law with variance $t$:
--
--   $$\operatorname{Law}_P(W_t)=\mathcal N(0,t).$$
--
--   Here `gaussianReal 0 t` denotes the Gaussian probability measure with mean $0$ and variance parameter $t$. The result includes the case $t=0$, where the law is concentrated at $0$.
--
--   This provides the one-time marginal required when relating the library's Brownian-motion construction to Mathlib's Brownian-motion predicates.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.BrownianMotion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasLaw_eval (W : BrownianMotion P) (t : ℝ≥0) :
--       HasLaw (W.W (t : ℝ)) (gaussianReal 0 t) P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/MathlibBridge`](https://prove2.me/theorems/9c49c388-9f09-41ff-9ebc-160632911f8f).
--
--   Definition modules: [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Previous: [`iIndep_of_indep_biSup_lt`](https://prove2.me/theorems/c904fc1b-c73f-4ae0-9449-c0e3258cf518) · Next: [`hasIndepIncrements`](https://prove2.me/theorems/f0b8f3c6-ac2e-4258-a88e-246cc3460201).
--
--   [Source excerpt, lines 68–69](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/MathlibBridge.lean#L68-L69) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/MathlibBridge.lean#L67-L85 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.MathlibBridge`, declaration `LevyStochCalc.Brownian.BrownianMotion.hasLaw_eval`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/MathlibBridge.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.BrownianMotion.hasLaw_eval_readable (W : BrownianMotion P) (t : ℝ≥0) :
    HasLaw (W.W (t : ℝ)) (gaussianReal 0 t) P := by sorry
