-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasIndepIncrements_readable
-- name    : LevyStochCalc.Brownian.BrownianMotion.hasIndepIncrements_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:53.662297+00:00
-- url     : https://prove2.me/theorems/f0b8f3c6-ac2e-4258-a88e-246cc3460201
-- title:
--   Independent Increments Of A Brownian Motion
-- statement:
--   Let $W$ be a Brownian motion on a probability space $(\Omega,P)$. Viewed at nonnegative times, the process $t\mapsto W_t$ has independent increments in the sense of `HasIndepIncrements`:
--
--   $$\operatorname{HasIndepIncrements}\bigl(t\mapsto W_t\bigr)\,P.$$
--
--   Equivalently, for every finite nondecreasing sequence of nonnegative times, the successive increments are mutually independent. This connects the project's Brownian-motion structure with the standard probability-theoretic independent-increments predicate.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.BrownianMotion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasIndepIncrements (W : BrownianMotion P) :
--       HasIndepIncrements (fun t : ℝ≥0 ↦ W.W t) P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/MathlibBridge`](https://prove2.me/theorems/9c49c388-9f09-41ff-9ebc-160632911f8f).
--
--   Definition modules: [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`iIndep_of_indep_biSup_lt`](https://prove2.me/theorems/c904fc1b-c73f-4ae0-9449-c0e3258cf518).
--
--   Previous: [`hasLaw_eval`](https://prove2.me/theorems/1fb6389e-a58c-4dab-9daf-eb1e551698b4).
--
--   [Source excerpt, lines 104–105](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/MathlibBridge.lean#L104-L105) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/MathlibBridge.lean#L103-L139 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.MathlibBridge`, declaration `LevyStochCalc.Brownian.BrownianMotion.hasIndepIncrements`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.BrownianMotion.hasIndepIncrements_readable (W : BrownianMotion P) :
    HasIndepIncrements (fun t : ℝ≥0 ↦ W.W t) P := by sorry
