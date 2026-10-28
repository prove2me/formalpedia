-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_dyadicTrunc_eventually_eq_readable
-- name    : LevyStochCalc.Brownian.Continuity.dyadicTrunc_eventually_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:27.831116+00:00
-- url     : https://prove2.me/theorems/3e1785d0-d93f-4be2-b07c-69e9627ca49e
-- title:
--   Eventual Stability of Dyadic Truncation
-- statement:
--   If s is a dyadic rational, then there exists L₀ : ℕ such that for every L ≥ L₀, its level-L dyadic truncation equals s:
--
--   $$s\in\operatorname{dyadicRationals}\Longrightarrow\exists L_0\,\forall L\ge L_0,\ \operatorname{dyadicTrunc}(L,s)=s.$$
--
--   The lemma `dyadicTrunc_eventually_eq_readable` records eventual exactness of truncation on the dense dyadic set.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma dyadicTrunc_eventually_eq {s : ℝ} (hs : s ∈ dyadicRationals) :
--       ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → dyadicTrunc L s = s
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Previous: [`dyadicTrunc_near_step`](https://prove2.me/theorems/cc514a95-7843-459b-984c-57d63cd24e90) · Next: [`exists_dyadic_scale`](https://prove2.me/theorems/1d383b87-9bce-4bea-947b-c6594626f115).
--
--   [Source excerpt, lines 312–313](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L312-L313) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L310-L325 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.dyadicTrunc_eventually_eq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)

lemma LevyStochCalc.Brownian.Continuity.dyadicTrunc_eventually_eq_readable {s : ℝ} (hs : s ∈ dyadicRationals) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → dyadicTrunc L s = s := by sorry
