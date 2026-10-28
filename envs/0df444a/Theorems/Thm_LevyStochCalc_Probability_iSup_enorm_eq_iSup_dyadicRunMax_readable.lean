-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_iSup_enorm_eq_iSup_dyadicRunMax_readable
-- name    : LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:07.048874+00:00
-- url     : https://prove2.me/theorems/acb0a4f1-b242-45cd-80de-139b129bb826
-- title:
--   Continuous Supremum from Dyadic Running Maxima
-- statement:
--   This vendored theorem identifies a continuous-time supremum with dyadic running maxima.
--
--   Let $T\geq0$, fix an outcome $\omega$, and suppose that the path $s\mapsto M_s(\omega)$ is right-continuous at every time. Then
--
--   $$
--   \sup_{t\in[0,T]}\|M_t(\omega)\|_{\mathrm{ENNReal}}
--   =
--   \sup_{n\in\mathbb N}
--   \|\operatorname{dyadicRunMax}(M,T,n,\omega)\|_{\mathrm{ENNReal}}.
--   $$
--
--   This is the pathwise bridge from discrete dyadic maximal estimates to a continuous-time supremum estimate.
--
--   **Formalization Note.** The supremum over $[0,T]$ is represented by an `iSup` over the subtype `Set.Icc 0 T`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem iSup_enorm_eq_iSup_dyadicRunMax (hT : 0 ≤ T) {ω : Ω}
--       (hcad : ∀ t : ℝ, Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t))
--         (nhds (M t ω))) :
--       (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞))
--         = ⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780).
--
--   Supporting theorems: [`enorm_dyadicRunMax`](https://prove2.me/theorems/df28b675-5880-4511-8fdc-de21a750c0cb), [`tendsto_dyadicTime_dyadicIndex`](https://prove2.me/theorems/5e110120-ccfd-4354-afb0-032615a35b6a).
--
--   Previous: [`tendsto_dyadicTime_dyadicIndex`](https://prove2.me/theorems/5e110120-ccfd-4354-afb0-032615a35b6a) · Next: [`lintegral_sq_dyadicRunMax_le`](https://prove2.me/theorems/c1b80434-c26c-49be-a883-841d52382ee6).
--
--   [Source excerpt, lines 208–212](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/DoobContinuous.lean#L208-L212) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/DoobContinuous.lean#L206-L241 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.DoobContinuous`, declaration `LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {M : ℝ → Ω → ℝ} {T : ℝ}

theorem LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax_readable (hT : 0 ≤ T) {ω : Ω}
    (hcad : ∀ t : ℝ, Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (M t ω))) :
    (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞))
      = ⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by sorry
