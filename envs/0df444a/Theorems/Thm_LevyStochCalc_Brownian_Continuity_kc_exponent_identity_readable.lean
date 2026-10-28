-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_exponent_identity_readable
-- name    : LevyStochCalc.Brownian.Continuity.kc_exponent_identity_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:27.528621+00:00
-- url     : https://prove2.me/theorems/015b3d90-70b0-4878-af84-3becbce9c7eb
-- title:
--   Kolmogorov–Chentsov Exponent Identity
-- statement:
--   This is an algebraic identity for the per-level Kolmogorov–Chentsov factor. For $\alpha,p,q\in\mathbb R$ and $n\in\mathbb N$,
--
--   $$
--   \frac{2^n\bigl((1/2)^n\bigr)^q}{\bigl(((1/2)^\alpha)^n\bigr)^p}
--   =\bigl((1/2)^{q-\alpha p-1}\bigr)^n.
--   $$
--
--   It isolates the geometric ratio governing summability of dyadic-level estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma kc_exponent_identity {α p q : ℝ} (n : ℕ) :
--       (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p
--         = ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Previous: [`rpow_half_pow_le`](https://prove2.me/theorems/4d94cc63-e21d-4250-be10-7ae322e82378) · Next: [`dyadic_holder_chaining`](https://prove2.me/theorems/749988d9-89e5-4fb5-9831-f2ad8915a549).
--
--   [Source excerpt, lines 381–383](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L381-L383) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L377-L400 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.kc_exponent_identity`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)

lemma LevyStochCalc.Brownian.Continuity.kc_exponent_identity_readable {α p q : ℝ} (n : ℕ) :
    (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p
      = ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n := by sorry
