-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_memLp_simpleIntegral_readable
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:56.211455+00:00
-- url     : https://prove2.me/theorems/7c5f50d8-edb5-487c-a4bf-6c19ad9a378c
-- title:
--   Square Integrability of a Simple Stochastic Integral
-- statement:
--   This is an $L^2$ regularity statement for an elementary stochastic integral.
--
--   Let $V$ be a Brownian motion, let $G$ be a simple predictable integrand on a time horizon $T$, and let $t\in\mathbb R$. Then
--   $$
--   \texttt{simpleIntegral}(V,G,t)\in L^2(P),
--   $$
--   that is, the function $\omega\mapsto\texttt{simpleIntegral}(V,G,t,\omega)$ has `MemLp` exponent $2$ with respect to $P$.
--
--   The lemma supplies the square-integrability hypothesis needed for pairings and limits of simple stochastic integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma memLp_simpleIntegral (V : BrownianMotion P) {T : ℝ} (G : SimplePredictable Ω T) (t : ℝ) :
--       MemLp (fun ω => simpleIntegral V G t ω) 2 P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossOrthogonalityLimit`](https://prove2.me/theorems/0a6cdcb3-be60-427a-8dc0-4862ed142b74).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Previous: [`integral_simpleIntegral_mul_eq_zero`](https://prove2.me/theorems/86d5362c-5613-4331-b577-05629cdbfba1) · Next: [`integral_mul_eq_zero_of_tendsto_eLpNorm`](https://prove2.me/theorems/9e82e98b-0377-41ae-b977-70c8c0709ea7).
--
--   [Source excerpt, lines 294–295](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L294-L295) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L293-L316 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossOrthogonalityLimit`, declaration `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
open LevyStochCalc.Brownian.Ito

lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral_readable (V : BrownianMotion P) {T : ℝ} (G : SimplePredictable Ω T) (t : ℝ) :
    MemLp (fun ω => simpleIntegral V G t ω) 2 P := by sorry
