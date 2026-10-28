-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_sum_xi_mul_simpleIntegral_sub_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.sum_xi_mul_simpleIntegral_sub_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:43.498981+00:00
-- url     : https://prove2.me/theorems/dfbfbaef-e395-42fa-a4db-142dc1f926ee
-- title:
--   Elementary Integral Against an Elementary Integral
-- statement:
--   Let $W$ be a Brownian motion, and let $G,K$ be simple predictable integrands with the same final partition point. For every time $t$ and sample point $ω$,
--
--   $$\sum_i G_i(ω)\left(I_K(\min(G_{i+1},t),ω)-I_K(\min(G_i,t),ω)\right)
--   =I_{G\cdot K}(t,ω),$$
--
--   where $I_K=\texttt{simpleIntegral}(W,K)$ and the product is formed on the common refinement. The equality is pointwise; the probability assumption on $P$ is present in the declaration but no almost-everywhere qualification occurs in the conclusion. This is the finite-partition associativity identity used to pass from elementary products to Itô-integral products.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem SimplePredictable.sum_xi_mul_simpleIntegral_sub
--       {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
--       {T : ℝ} (G K : SimplePredictable Ω T)
--       (h_eq : G.partition (Fin.last G.N) = K.partition (Fin.last K.N))
--       (t : ℝ) (ω : Ω) :
--       (∑ i : Fin G.N, G.ξ i ω *
--           (simpleIntegral W K (min (G.partition i.succ) t) ω
--             - simpleIntegral W K (min (G.partition i.castSucc) t) ω))
--         = simpleIntegral W (G.mul_on_common K h_eq) t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraProduct`](https://prove2.me/theorems/99205bea-847c-43ba-a041-1e0384d4d19c).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Previous: [`SimplePredictable.eval_mul_on_common`](https://prove2.me/theorems/0eb3f171-e89b-4176-adbc-20be9554ddb1) · Next: [`SimplePredictable.appendInterval_integralAgainst`](https://prove2.me/theorems/9a670acc-4886-40c7-9771-97961383f589).
--
--   [Source excerpt, lines 115–123](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraProduct.lean#L115-L123) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraProduct.lean#L112-L201 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraProduct`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.sum_xi_mul_simpleIntegral_sub`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.sum_xi_mul_simpleIntegral_sub_readable
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (G K : SimplePredictable Ω T)
    (h_eq : G.partition (Fin.last G.N) = K.partition (Fin.last K.N))
    (t : ℝ) (ω : Ω) :
    (∑ i : Fin G.N, G.ξ i ω *
        (simpleIntegral W K (min (G.partition i.succ) t) ω
          - simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = simpleIntegral W (G.mul_on_common K h_eq) t ω := by sorry
