-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_abs_eval_le_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.abs_eval_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:56.819973+00:00
-- url     : https://prove2.me/theorems/1cd600b6-5e8b-4337-a77d-6ea63c207357
-- title:
--   Bounded Evaluation of a Simple Predictable Integrand
-- statement:
--   This technical lemma bounds every evaluation of a simple predictable integrand by a uniform coefficient bound.
--
--   Let $H$ be a `SimplePredictable` integrand on $\Omega$ with time horizon $T$, and let $C\ge0$. Assume that every coefficient $\xi_i(\omega)$ satisfies $|\xi_i(\omega)|\le C$ for every tile index $i$ and every $\omega\in\Omega$. Then, for every time $s\in\mathbb R$ and every $\omega\in\Omega$,
--
--   $$
--   |H.\operatorname{eval}(s,\omega)|\le C.
--   $$
--
--   The statement uses the Lean definition `SimplePredictable.eval`. It also covers times outside all partition tiles, where the evaluation is zero. This bound is used to transfer coefficient bounds to the associated elementary integral.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem SimplePredictable.abs_eval_le {T : ℝ} (H : SimplePredictable Ω T) {C : ℝ} (hC0 : 0 ≤ C)
--       (hC : ∀ (i : Fin H.N) (ω : Ω), |H.ξ i ω| ≤ C) (s : ℝ) (ω : Ω) : |H.eval s ω| ≤ C
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoIncrementMomentRestrict`](https://prove2.me/theorems/6729fab9-4d54-4cac-a286-3a20b472164d).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb).
--
--   Next: [`SimplePredictable.varClock_le_Ioc`](https://prove2.me/theorems/439559a5-0cc2-4a3a-a3c2-a6d24460420f).
--
--   [Source excerpt, lines 60–61](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean#L60-L61) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean#L59-L73 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoIncrementMomentRestrict`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.abs_eval_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentRestrict

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.abs_eval_le_readable {T : ℝ} (H : SimplePredictable Ω T) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (i : Fin H.N) (ω : Ω), |H.ξ i ω| ≤ C) (s : ℝ) (ω : Ω) : |H.eval s ω| ≤ C := by sorry
