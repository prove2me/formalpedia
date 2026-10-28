-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_exists_readable
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:10.647909+00:00
-- url     : https://prove2.me/theorems/7d8b284a-c9b3-4927-9d3c-74473785d55c
-- title:
--   Existence Of A $d$-Dimensional Brownian Motion
-- statement:
--   For every natural number $d$, there exist a measurable space $\Omega$, a probability measure $P$ on it, and a $d$-dimensional Brownian motion:
--
--   $$\forall d\in\mathbb N,\quad \exists(\Omega,P),\ \operatorname{IsProbabilityMeasure}(P)\land\operatorname{Nonempty}(\operatorname{MultidimBrownianMotion}(P,d)).$$
--
--   The statement includes $d=0$ and imposes no positivity condition on $d$. It is an existence result for a probability space with $d$ independent Brownian coordinates and jointly continuous paths.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Multidim`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem MultidimBrownianMotion.exists (d : ℕ) :
--       ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
--         (_ : IsProbabilityMeasure P), Nonempty (MultidimBrownianMotion P d)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3).
--
--   Supporting theorems: [`BrownianMotion.exists`](https://prove2.me/theorems/d52e5c72-47ca-41b1-83e3-5e8da38f1f08).
--
--   [Source excerpt, lines 179–181](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/Multidim.lean#L179-L181) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/Multidim.lean#L173-L218 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.Multidim`, declaration `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Multidim

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/Multidim.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u

theorem LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_readable (d : ℕ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (MultidimBrownianMotion P d) := by sorry
