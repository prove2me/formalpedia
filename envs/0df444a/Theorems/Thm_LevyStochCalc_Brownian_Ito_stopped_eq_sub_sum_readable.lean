-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stopped_eq_sub_sum_readable
-- name    : LevyStochCalc.Brownian.Ito.stopped_eq_sub_sum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:23.338868+00:00
-- url     : https://prove2.me/theorems/ca6db2c8-b052-412e-99f9-f5b6637e3786
-- title:
--   Pathwise Decomposition of a Finite-Range Stopped Integrand
-- statement:
--   This is the pathwise decomposition of the cut integrand used for finite-range optional stopping.
--
--   Let $\tau:\Omega\to\operatorname{WithTop}(\mathbb R)$, let $H:\Omega\times\mathbb R\to\mathbb R$, let $t\in\mathbb R$, and let $J$ be a finite set of real times. Assume:
--
--   1. every $c\in J$ satisfies $0\le c$;
--   2. every $c\in J$ satisfies $c<t$;
--   3. for every $\omega$, either $\tau(\omega)=c$ for some $c\in J$, or $t\le\tau(\omega)$.
--
--   Then the indicator-term representation `indTerm` of the stopped integrand `Probability.stopped τ H` on $(0,t]$ is pointwise
--   $$
--   \operatorname{indTerm}(\operatorname{stopped}(\tau,H),0,t)(\omega,s)
--   =
--   \operatorname{indTerm}(H,0,t)(\omega,s)
--   -\sum_{c\in J}\operatorname{cutTerm}(\tau,H,c,t)(\omega,s).
--   $$
--
--   This neutral pathwise identity is the algebraic component of the finite-range optional-stopping theorem.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stopped_eq_sub_sum (H : Ω → ℝ → ℝ) {t : ℝ} (J : Finset ℝ)
--       (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
--       (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
--       indTerm (Probability.stopped τ H) 0 t
--         = fun ω s => indTerm H 0 t ω s - ∑ c ∈ J, cutTerm τ H c t ω s
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoOptionalStopping`](https://prove2.me/theorems/1d25c358-1966-4cac-ba37-96d7bf5aaf7d).
--
--   Definition modules: [`LevyStochCalc/Probability/StoppedProgressive`](https://prove2.me/theorems/602d883b-27f9-43ed-bb5c-77dd184db556).
--
--   Next: [`stochasticIntegralBrownian_stopped`](https://prove2.me/theorems/ed4209dc-2e3a-4843-8705-dade9e7c1cbc).
--
--   [Source excerpt, lines 143–147](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoOptionalStopping.lean#L143-L147) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoOptionalStopping.lean#L139-L209 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoOptionalStopping`, declaration `LevyStochCalc.Brownian.Ito.stopped_eq_sub_sum`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoOptionalStopping

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoOptionalStopping.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
variable (τ : Ω → WithTop ℝ)
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.stopped_eq_sub_sum_readable (H : Ω → ℝ → ℝ) {t : ℝ} (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    indTerm (Probability.stopped τ H) 0 t
      = fun ω s => indTerm H 0 t ω s - ∑ c ∈ J, cutTerm τ H c t ω s := by sorry
