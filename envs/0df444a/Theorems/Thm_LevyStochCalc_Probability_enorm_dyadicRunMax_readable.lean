-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_enorm_dyadicRunMax_readable
-- name    : LevyStochCalc.Probability.enorm_dyadicRunMax_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:57.435954+00:00
-- url     : https://prove2.me/theorems/df28b675-5880-4511-8fdc-de21a750c0cb
-- title:
--   Extended Norm of the Dyadic Running Maximum
-- statement:
--   This vendored theorem identifies the extended norm of a sampled running maximum.
--
--   For a real-valued process $M_t(\omega)$, a horizon $T$, a level $n\in\mathbb N$, and an outcome $\omega$, the `ENNReal` norm of `dyadicRunMax M T n ω` equals the supremum over the $2^n+1$ dyadic partition points:
--
--   $$
--   \|\operatorname{dyadicRunMax}(M,T,n,\omega)\|_{\mathrm{ENNReal}}
--   =
--   \sup_{k\in\operatorname{Fin}(2^n+1)}
--   \|M_{\operatorname{dyadicTime}(T,n,k)}(\omega)\|_{\mathrm{ENNReal}}.
--   $$
--
--   This provides the discrete supremum representation used in continuous-time maximal estimates.
--
--   **Formalization Note.** The supremum is an `ENNReal` supremum of the coerced nonnegative norms.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem enorm_dyadicRunMax (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
--       (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)
--         = ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780).
--
--   Next: [`tendsto_dyadicTime_dyadicIndex`](https://prove2.me/theorems/5e110120-ccfd-4354-afb0-032615a35b6a).
--
--   [Source excerpt, lines 111–113](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/DoobContinuous.lean#L111-L113) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/DoobContinuous.lean#L109-L128 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.DoobContinuous`, declaration `LevyStochCalc.Probability.enorm_dyadicRunMax`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem LevyStochCalc.Probability.enorm_dyadicRunMax_readable (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)
      = ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by sorry
