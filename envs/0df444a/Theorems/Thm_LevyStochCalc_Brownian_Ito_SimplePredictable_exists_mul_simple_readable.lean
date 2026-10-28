-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_exists_mul_simple_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:48.229486+00:00
-- url     : https://prove2.me/theorems/2d890f64-d894-41e2-b8b4-bc4a0edaf483
-- title:
--   Existence of an Adapted Simple Product
-- statement:
--   Let $W$ be a Brownian motion, let $ℱ$ be a filtration, and let $G,K$ be simple predictable integrands with arbitrary horizons. Assume every coefficient of $G$ and $K$ is strongly measurable with respect to the filtration at its preceding partition time.
--
--   Then there exist a horizon $T₃$ and a simple predictable integrand $Q$ on that horizon such that: (1) every coefficient of $Q$ is adapted and strongly measurable; (2) for all $s,ω$, $Q(s,ω)=G(s,ω)K(s,ω)$; and (3) for all $t,ω$,
--
--   $$\texttt{integralAgainst}(G,\texttt{simpleIntegral}(W,K),t,ω)=\texttt{simpleIntegral}(W,Q,t,ω).$$
--
--   The statement is existential because the common horizon and refinement are constructed from the two original horizons. It provides closure of simple predictable integrands under products.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem SimplePredictable.exists_mul_simple
--       {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
--       {T₁ T₂ : ℝ} (G : SimplePredictable Ω T₁) (K : SimplePredictable Ω T₂)
--       (h_adaptG : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ (G.partition i.castSucc)) (G.ξ i))
--       (h_adaptK : ∀ i : Fin K.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ (K.partition i.castSucc)) (K.ξ i)) :
--       ∃ (T₃ : ℝ) (Q : SimplePredictable Ω T₃),
--         (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--           (ℱ (Q.partition i.castSucc)) (Q.ξ i))
--         ∧ (∀ s ω, Q.eval s ω = G.eval s ω * K.eval s ω)
--         ∧ (∀ t ω, G.integralAgainst (fun u ω' => simpleIntegral W K u ω') t ω
--             = simpleIntegral W Q t ω)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraProduct`](https://prove2.me/theorems/99205bea-847c-43ba-a041-1e0384d4d19c).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`SimplePredictable.appendInterval_integralAgainst`](https://prove2.me/theorems/9a670acc-4886-40c7-9771-97961383f589), [`SimplePredictable.eval_mul_on_common`](https://prove2.me/theorems/0eb3f171-e89b-4176-adbc-20be9554ddb1), [`SimplePredictable.sum_xi_mul_simpleIntegral_sub`](https://prove2.me/theorems/dfbfbaef-e395-42fa-a4db-142dc1f926ee).
--
--   Previous: [`SimplePredictable.appendInterval_integralAgainst`](https://prove2.me/theorems/9a670acc-4886-40c7-9771-97961383f589).
--
--   [Source excerpt, lines 284–297](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraProduct.lean#L284-L297) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraProduct.lean#L280-L321 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraProduct`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple_readable
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T₁ T₂ : ℝ} (G : SimplePredictable Ω T₁) (K : SimplePredictable Ω T₂)
    (h_adaptG : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    (h_adaptK : ∀ i : Fin K.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (K.partition i.castSucc)) (K.ξ i)) :
    ∃ (T₃ : ℝ) (Q : SimplePredictable Ω T₃),
      (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (Q.partition i.castSucc)) (Q.ξ i))
      ∧ (∀ s ω, Q.eval s ω = G.eval s ω * K.eval s ω)
      ∧ (∀ t ω, G.integralAgainst (fun u ω' => simpleIntegral W K u ω') t ω
          = simpleIntegral W Q t ω) := by sorry
