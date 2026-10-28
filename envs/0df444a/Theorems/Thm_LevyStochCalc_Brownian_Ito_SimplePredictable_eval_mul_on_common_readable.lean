-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_eval_mul_on_common_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.eval_mul_on_common_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:51.354468+00:00
-- url     : https://prove2.me/theorems/0eb3f171-e89b-4176-adbc-20be9554ddb1
-- title:
--   Evaluation of a Product on a Common Refinement
-- statement:
--   Let $H₁,H₂$ be simple predictable integrands with equal final partition points. Their common-refinement product `H₁.mul_on_common H₂ h_eq` evaluates pointwise as the product of their evaluations:
--
--   $$\texttt{eval}(H₁\texttt{.mul\_on\_common}\ H₂,s,ω)=\texttt{eval}(H₁,s,ω)\,\texttt{eval}(H₂,s,ω).$$
--
--   The conclusion holds for every $s∈ℝ$ and $ω∈Ω$. The result is purely finite-dimensional partition algebra and is used to represent products as simple integrands.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem SimplePredictable.eval_mul_on_common
--       {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
--       (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
--       (s : ℝ) (ω : Ω) :
--       (H₁.mul_on_common H₂ h_eq).eval s ω = H₁.eval s ω * H₂.eval s ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraProduct`](https://prove2.me/theorems/99205bea-847c-43ba-a041-1e0384d4d19c).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb).
--
--   Supporting theorems: [`sum_ite_mul_sum_ite`](https://prove2.me/theorems/7b3182dd-5410-4504-8fdb-fdf2d08f8bb4).
--
--   Previous: [`sum_ite_mul_sum_ite`](https://prove2.me/theorems/7b3182dd-5410-4504-8fdb-fdf2d08f8bb4) · Next: [`SimplePredictable.sum_xi_mul_simpleIntegral_sub`](https://prove2.me/theorems/dfbfbaef-e395-42fa-a4db-142dc1f926ee).
--
--   [Source excerpt, lines 83–87](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraProduct.lean#L83-L87) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraProduct.lean#L82-L103 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraProduct`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.eval_mul_on_common`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.eval_mul_on_common_readable
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (s : ℝ) (ω : Ω) :
    (H₁.mul_on_common H₂ h_eq).eval s ω = H₁.eval s ω * H₂.eval s ω := by sorry
