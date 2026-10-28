-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_dense_dyadicRationals_readable
-- name    : LevyStochCalc.Brownian.Continuity.dense_dyadicRationals_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:15.853543+00:00
-- url     : https://prove2.me/theorems/85782cfc-fe1d-4e3d-b7b8-39bea04a659f
-- title:
--   Density of Dyadic Rationals
-- statement:
--   The set `dyadicRationals = {k·2^{-n} : k ∈ ℤ, n ∈ ℕ}` is dense in ℝ. Equivalently, every real x and every radius r > 0 admit a dyadic rational within distance r of x. The lemma `dense_dyadicRationals_readable` supplies the dense domain used in the deterministic Kolmogorov–Chentsov extension argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Continuity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma dense_dyadicRationals : Dense dyadicRationals
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ContinuityDyadicChaining`](https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3).
--
--   Next: [`dyadicTrunc_succ_step`](https://prove2.me/theorems/f1f03a2a-9f1b-43c6-84e0-395a9ea8ebbc).
--
--   [Source excerpt, lines 120–120](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L120-L120) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L117-L150 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, declaration `LevyStochCalc.Brownian.Continuity.dense_dyadicRationals`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)

lemma LevyStochCalc.Brownian.Continuity.dense_dyadicRationals_readable : Dense dyadicRationals := by sorry
