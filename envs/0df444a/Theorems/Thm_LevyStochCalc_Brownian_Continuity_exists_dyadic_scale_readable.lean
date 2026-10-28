-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_exists_dyadic_scale_readable
-- name    : LevyStochCalc.Brownian.Continuity.exists_dyadic_scale_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:22.580987+00:00
-- url     : https://prove2.me/theorems/1d383b87-9bce-4bea-947b-c6594626f115
-- title:
--   Dyadic Scale Selection
-- statement:
--   This is a deterministic dyadic-scale selection lemma. For a real number $d$ satisfying $0<d\le 1$, there exists $m\in\mathbb N$ such that
--
--   $$
--   (1/2)^{m+1}<d\le (1/2)^m.
--   $$
--
--   The result provides the discrete scale used to compare an arbitrary distance with dyadic levels in chaining arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma exists_dyadic_scale {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
--       ∃ m : ℕ, (1 / 2 : ℝ) ^ (m + 1) < d ∧ d ≤ (1 / 2) ^ m
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Previous: [`dyadicTrunc_eventually_eq`](https://prove2.me/theorems/3e1785d0-d93f-4be2-b07c-69e9627ca49e) · Next: [`rpow_half_pow_le`](https://prove2.me/theorems/4d94cc63-e21d-4250-be10-7ae322e82378).
--
--   [Source excerpt, lines 341–342](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L341-L342) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L339-L355 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.exists_dyadic_scale`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)

lemma LevyStochCalc.Brownian.Continuity.exists_dyadic_scale_readable {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ∃ m : ℕ, (1 / 2 : ℝ) ^ (m + 1) < d ∧ d ≤ (1 / 2) ^ m := by sorry
