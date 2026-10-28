-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_rpow_half_pow_le_readable
-- name    : LevyStochCalc.Brownian.Continuity.rpow_half_pow_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:30.62299+00:00
-- url     : https://prove2.me/theorems/4d94cc63-e21d-4250-be10-7ae322e82378
-- title:
--   Dyadic Power Comparison
-- statement:
--   This is a deterministic comparison between dyadic scales and Hölder powers. Let $\alpha,d\in\mathbb R$ and $m\in\mathbb N$. If $\alpha>0$ and $(1/2)^{m+1}<d$, then
--
--   $$
--   \bigl((1/2)^\alpha\bigr)^m\le 2^\alpha d^\alpha.
--   $$
--
--   It converts a geometric level factor into a power of the underlying distance, with no probabilistic assumptions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma rpow_half_pow_le {α : ℝ} (hα : 0 < α) {d : ℝ} (m : ℕ)
--       (hd : (1 / 2 : ℝ) ^ (m + 1) < d) :
--       ((1 / 2 : ℝ) ^ α) ^ m ≤ (2 : ℝ) ^ α * d ^ α
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Previous: [`exists_dyadic_scale`](https://prove2.me/theorems/1d383b87-9bce-4bea-947b-c6594626f115) · Next: [`kc_exponent_identity`](https://prove2.me/theorems/015b3d90-70b0-4878-af84-3becbce9c7eb).
--
--   [Source excerpt, lines 359–361](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L359-L361) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L357-L375 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.rpow_half_pow_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)

lemma LevyStochCalc.Brownian.Continuity.rpow_half_pow_le_readable {α : ℝ} (hα : 0 < α) {d : ℝ} (m : ℕ)
    (hd : (1 / 2 : ℝ) ^ (m + 1) < d) :
    ((1 / 2 : ℝ) ^ α) ^ m ≤ (2 : ℝ) ^ α * d ^ α := by sorry
