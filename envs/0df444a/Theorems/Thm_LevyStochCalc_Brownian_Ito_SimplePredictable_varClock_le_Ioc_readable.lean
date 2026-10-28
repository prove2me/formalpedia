-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_varClock_le_Ioc_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_le_Ioc_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:09.401172+00:00
-- url     : https://prove2.me/theorems/439559a5-0cc2-4a3a-a3c2-a6d24460420f
-- title:
--   Variance Budget of Tiles Inside an Interval
-- statement:
--   This theorem bounds the variance clock of tiles contained in an interval.
--
--   Let $H$ be a simple predictable integrand with partition times, and let $a\le b$. Define the per-tile bound to be $C$ when the tile lies inside $(a,b]$, meaning $a\le\tau_j$ and $\tau_{j+1}\le b$, and $0$ otherwise. Then
--
--   $$
--   \operatorname{varClock}\!\left(H,\,j\mapsto
--   \begin{cases}C,&a\le\tau_j\text{ and }\tau_{j+1}\le b,\\0,&\text{otherwise,}
--   \end{cases}\!,N\right)
--   \le C^2(b-a).
--   $$
--
--   This estimate is the deterministic localization step behind moment bounds for integrands restricted to $(a,b]$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem SimplePredictable.varClock_le_Ioc {T : ℝ} (H : SimplePredictable Ω T) {a b C : ℝ}
--       (hab : a ≤ b) :
--       H.varClock (fun j => if a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b then C else 0)
--           H.N ≤ C ^ 2 * (b - a)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoIncrementMomentRestrict`](https://prove2.me/theorems/6729fab9-4d54-4cac-a286-3a20b472164d).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3).
--
--   Previous: [`SimplePredictable.abs_eval_le`](https://prove2.me/theorems/1cd600b6-5e8b-4337-a77d-6ea63c207357) · Next: [`SimplePredictable.exists_restrict_Ioc`](https://prove2.me/theorems/5e9d641c-78ce-4154-aba8-1c8bbbf578e0).
--
--   [Source excerpt, lines 76–79](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean#L76-L79) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean#L75-L134 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoIncrementMomentRestrict`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_le_Ioc`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentRestrict

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_le_Ioc_readable {T : ℝ} (H : SimplePredictable Ω T) {a b C : ℝ}
    (hab : a ≤ b) :
    H.varClock (fun j => if a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b then C else 0)
        H.N ≤ C ^ 2 * (b - a) := by sorry
