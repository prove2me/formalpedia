-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIoc_zero_eval_readable
-- name    : LevyStochCalc.Brownian.Ito.stepIoc_zero_eval_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:44.8719+00:00
-- url     : https://prove2.me/theorems/2c0d5744-8278-417f-9f9c-dd287d9c0a4f
-- title:
--   Evaluation of the Initial Step Integrand
-- statement:
--   Let $b>0$, let $s∈ℝ$, and let $ω∈Ω$. The elementary step integrand `stepIoc₀ Ω hb`, associated with the interval $(0,b]$, evaluates as the indicator of that interval:
--
--   $$\texttt{stepIoc₀}(s,ω)=\mathbf{1}_{(0,b]}(s).$$
--
--   Equivalently, the value is $1$ when $0<s≤b$ and $0$ otherwise. The sample point $ω$ is arbitrary because the step coefficient is constant in $ω$. This is an algebraic evaluation lemma for simple predictable integrands.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stepIoc₀_eval {b : ℝ} (hb : 0 < b) (s : ℝ) (ω : Ω) :
--       (stepIoc₀ Ω hb).eval s ω = (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraAssociativity`](https://prove2.me/theorems/738b1003-832c-420c-a910-2008630209bc).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb).
--
--   Previous: [`stepIoc_eval`](https://prove2.me/theorems/229a87fb-276d-451b-880f-3ee228acc687) · Next: [`stochasticIntegralBrownian_indicator_Ioc`](https://prove2.me/theorems/bcc8c011-e83f-4b9e-a0e6-5de008451e39).
--
--   [Source excerpt, lines 320–321](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean#L320-L321) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraAssociativity`, declaration `LevyStochCalc.Brownian.Ito.stepIoc₀_eval`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean, lines 320-333). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.stepIoc_zero_eval_readable {b : ℝ} (hb : 0 < b) (s : ℝ) (ω : Ω) :
    (stepIoc₀ Ω hb).eval s ω = (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s := by sorry
