-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_tendsto_dyadicTime_dyadicIndex_readable
-- name    : LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:57.447979+00:00
-- url     : https://prove2.me/theorems/5e110120-ccfd-4354-afb0-032615a35b6a
-- title:
--   Rightward Convergence of Dyadic Sampling Points
-- statement:
--   This vendored convergence theorem concerns dyadic sampling of a time point.
--
--   Let $T>0$ and let $t\in[0,T]$. For each $n$, let `dyadicIndex T t n` select the dyadic point at level $n$ lying at or to the right of $t$. Then
--
--   $$
--   \operatorname{dyadicTime}(T,n,\operatorname{dyadicIndex}(T,t,n))
--   \longrightarrow t
--   $$
--
--   as $n\to\infty$, with convergence in the neighborhood filter of $t$ restricted to $[t,\infty)$.
--
--   The result supplies the time approximation needed to pass from dyadic samples to right-continuous paths.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_dyadicTime_dyadicIndex {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) :
--       Filter.Tendsto (fun n => dyadicTime T n (dyadicIndex T t n)) Filter.atTop
--         (nhdsWithin t (Set.Ici t))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780).
--
--   Previous: [`enorm_dyadicRunMax`](https://prove2.me/theorems/df28b675-5880-4511-8fdc-de21a750c0cb) · Next: [`iSup_enorm_eq_iSup_dyadicRunMax`](https://prove2.me/theorems/acb0a4f1-b242-45cd-80de-139b129bb826).
--
--   [Source excerpt, lines 187–189](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/DoobContinuous.lean#L187-L189) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/DoobContinuous.lean#L186-L204 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.DoobContinuous`, declaration `LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex_readable {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) :
    Filter.Tendsto (fun n => dyadicTime T n (dyadicIndex T t n)) Filter.atTop
      (nhdsWithin t (Set.Ici t)) := by sorry
