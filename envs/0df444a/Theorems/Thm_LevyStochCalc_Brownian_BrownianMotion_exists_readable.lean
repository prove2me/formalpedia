-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_exists_readable
-- name    : LevyStochCalc.Brownian.BrownianMotion.exists_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:40.729491+00:00
-- url     : https://prove2.me/theorems/d52e5c72-47ca-41b1-83e3-5e8da38f1f08
-- title:
--   Existence Of A Probability Space Carrying Brownian Motion
-- statement:
--   There exist a type $\Omega$, a measurable-space structure on $\Omega$, a probability measure $P$ on $\Omega$, and a Brownian motion with law $P$:
--
--   $$\exists\Omega,\ \exists P,\ \operatorname{IsProbabilityMeasure}(P),\ \operatorname{Nonempty}(\operatorname{BrownianMotion}(P)).$$
--
--   The theorem supplies existence of at least one probability space carrying a Brownian motion, with no prescribed sample space or measure. It provides the foundational one-dimensional Brownian construction used by later product constructions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem BrownianMotion.exists :
--       ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
--         (_ : IsProbabilityMeasure P), Nonempty (BrownianMotion P)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/Existence`](https://prove2.me/theorems/10f8be28-ef23-4221-869d-2a746f8fe042).
--
--   Definition modules: [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   [Source excerpt, lines 106–108](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/Existence.lean#L106-L108) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/Existence.lean#L104-L119 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.Existence`, declaration `LevyStochCalc.Brownian.BrownianMotion.exists`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Existence

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/Existence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u

theorem LevyStochCalc.Brownian.BrownianMotion.exists_readable :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (BrownianMotion P) := by sorry
