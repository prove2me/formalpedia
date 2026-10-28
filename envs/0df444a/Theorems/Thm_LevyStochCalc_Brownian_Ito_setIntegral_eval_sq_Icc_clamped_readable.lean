-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_setIntegral_eval_sq_Icc_clamped_readable
-- name    : LevyStochCalc.Brownian.Ito.setIntegral_eval_sq_Icc_clamped_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:20.491428+00:00
-- url     : https://prove2.me/theorems/264a25e4-219e-44a6-9deb-bfc553ff7dd9
-- title:
--   Clamped Simple-Integrand Square Integral
-- statement:
--   This technical identity concerns a simple predictable integrand $G$ on a measurable space $(\Omega,\mathcal F)$, a point $\omega\in\Omega$, a horizon parameter $T\in\mathbb R$, and a time $t\in\mathbb R$. Writing $p_i=G.\mathrm{partition}(i)$, $\xi_i=G.\xi(i,\omega)$, and $G.\mathrm{eval}(u,\omega)$ for the integrand value, the real integral over the interval $[0,t]$ equals the partition sum
--
--   $$\int_{[0,t]} G.\mathrm{eval}(u,\omega)^2\,du
--   =\sum_{i\in\mathrm{Fin}(G.N)}\bigl(\min(p_{i+1},t)-\min(p_i,t)\bigr)\xi_i^2.$$
--
--   The clamping by minima makes each partition length nonnegative, including when $t<0$. This is the real-valued companion of the corresponding nonnegative integral formula and provides a closed sum representation for the simple-level compensator.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma setIntegral_eval_sq_Icc_clamped {T : ℝ} (G : SimplePredictable Ω T) (ω : Ω)
--       {t : ℝ} :
--       ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume
--         = ∑ i : Fin G.N,
--           (min (G.partition i.succ) t - min (G.partition i.castSucc) t) * (G.ξ i ω) ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoL2CompletionCompensator`](https://prove2.me/theorems/11b95172-ce21-4778-ae54-6649149ee1fc).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb).
--
--   Previous: [`simpleIntegral_sub_sq_bochner_clamped_weighted`](https://prove2.me/theorems/9fca8288-f73b-4ee9-a521-8212a2c93f44) · Next: [`martingale_simpleIntegral_sq_sub_compensator`](https://prove2.me/theorems/76ba9e80-d221-4784-b289-e962828cbbfd).
--
--   [Source excerpt, lines 288–292](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean#L288-L292) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean#L283-L317 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionCompensator`, declaration `LevyStochCalc.Brownian.Ito.setIntegral_eval_sq_Icc_clamped`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Ito.setIntegral_eval_sq_Icc_clamped_readable {T : ℝ} (G : SimplePredictable Ω T) (ω : Ω)
    {t : ℝ} :
    ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume
      = ∑ i : Fin G.N,
        (min (G.partition i.succ) t - min (G.partition i.castSucc) t) * (G.ξ i ω) ^ 2 := by sorry
