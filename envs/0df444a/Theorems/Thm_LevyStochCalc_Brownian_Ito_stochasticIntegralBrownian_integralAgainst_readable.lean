-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_integralAgainst_readable
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:52.218396+00:00
-- url     : https://prove2.me/theorems/ad605701-48f4-400c-83de-f35b5212c9ce
-- title:
--   Associativity Against a Simple Predictable Integrand
-- statement:
--   Let $W$ be a Brownian motion with Brownian filtration, let $G$ be a simple predictable integrand with adapted strongly measurable coefficients, and let $H:Ω×ℝ→ℝ$ be jointly measurable, progressively measurable, and of finite squared `ENNReal` energy on every positive time interval. Assume also that the product $G(s,ω)H(ω,s)$ is jointly measurable, progressively measurable, and has finite squared energy on every positive time interval.
--
--   For every $t>0$,
--
--   $$\texttt{integralAgainst}(G,\texttt{stochasticIntegralBrownian}(H),t)
--   =\texttt{stochasticIntegralBrownian}(G\,H,t)\quad P\text{-almost everywhere}.$$
--
--   This is the associativity law between an elementary integral against the Itô integral and the Itô integral of the product. The strict positivity assumption on $t$ is part of the statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stochasticIntegralBrownian_integralAgainst {t : ℝ} (ht : 0 < t) :
--       G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t
--         =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
--           hmm hmp hmq t
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraAssociativity`](https://prove2.me/theorems/738b1003-832c-420c-a910-2008630209bc).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/ItoAlgebraProduct`](https://prove2.me/theorems/99205bea-847c-43ba-a041-1e0384d4d19c), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`SimplePredictable.exists_mul_simple`](https://prove2.me/theorems/2d890f64-d894-41e2-b8b4-bc4a0edaf483), [`SimplePredictable.lintegral_eval_sq_lt_top`](https://prove2.me/theorems/1a3d860d-d849-45a8-9155-ad2dbfbcdfa6), [`stochasticIntegralBrownian_eval_simple`](https://prove2.me/theorems/cae7fbf2-3586-459d-92c8-a9b6a264de7f).
--
--   Next: [`stepIoc_eval`](https://prove2.me/theorems/229a87fb-276d-451b-880f-3ee228acc687).
--
--   [Source excerpt, lines 58–61](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean#L58-L61) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraAssociativity`, declaration `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean, lines 54-269). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hmm : Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s))
  (hmp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s)
  (hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ h_adapt

theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_readable {t : ℝ} (ht : 0 < t) :
    G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
        hmm hmp hmq t := by sorry
