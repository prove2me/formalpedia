-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIoc_eval_readable
-- name    : LevyStochCalc.Brownian.Ito.stepIoc_eval_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:06.765931+00:00
-- url     : https://prove2.me/theorems/229a87fb-276d-451b-880f-3ee228acc687
-- title:
--   Evaluation of an Interval Step Integrand
-- statement:
--   Let $0<a<b$, let $s∈ℝ$, and let $ω∈Ω$. The elementary step integrand `stepIoc Ω ha hab`, associated with $(a,b]$, evaluates to the indicator of that interval:
--
--   $$\texttt{stepIoc}(s,ω)=\mathbf{1}_{(a,b]}(s).$$
--
--   Thus the value is $1$ exactly when $a<s≤b$, and is $0$ otherwise. The result is pointwise in both $s$ and $ω$ and is used to identify localized elementary integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stepIoc_eval {a b : ℝ} (ha : 0 < a) (hab : a < b) (s : ℝ) (ω : Ω) :
--       (stepIoc Ω ha hab).eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraAssociativity`](https://prove2.me/theorems/738b1003-832c-420c-a910-2008630209bc).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb).
--
--   Previous: [`stochasticIntegralBrownian_integralAgainst`](https://prove2.me/theorems/ad605701-48f4-400c-83de-f35b5212c9ce) · Next: [`stepIoc₀_eval`](https://prove2.me/theorems/2c0d5744-8278-417f-9f9c-dd287d9c0a4f).
--
--   [Source excerpt, lines 304–305](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean#L304-L305) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraAssociativity`, declaration `LevyStochCalc.Brownian.Ito.stepIoc_eval`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean, lines 304-318). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.stepIoc_eval_readable {a b : ℝ} (ha : 0 < a) (hab : a < b) (s : ℝ) (ω : Ω) :
    (stepIoc Ω ha hab).eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s := by sorry
