-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_appendInterval_integralAgainst_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.appendInterval_integralAgainst_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:22.901218+00:00
-- url     : https://prove2.me/theorems/9a670acc-4886-40c7-9771-97961383f589
-- title:
--   Zero Extension Preserves Elementary Integrals
-- statement:
--   Let $G$ be a simple predictable integrand with horizon $T$, let $T'$ be later than its final partition point, and let $M:ℝ→Ω→ℝ$ be any process. The zero-extended integrand `G.appendInterval hlt` has the same elementary integral against $M$ at every time $t$ and sample point $ω$:
--
--   $$\texttt{integralAgainst}(G\texttt{.appendInterval},M,t,ω)=\texttt{integralAgainst}(G,M,t,ω).$$
--
--   The equality is pointwise and requires no measurability or probabilistic assumptions on $M$. This bookkeeping lemma permits simple integrands with different horizons to be placed on a common terminal partition.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem SimplePredictable.appendInterval_integralAgainst
--       {T : ℝ} (G : SimplePredictable Ω T) {T' : ℝ}
--       (hlt : G.partition (Fin.last G.N) < T') (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
--       (G.appendInterval hlt).integralAgainst M t ω = G.integralAgainst M t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraProduct`](https://prove2.me/theorems/99205bea-847c-43ba-a041-1e0384d4d19c).
--
--   Definition modules: [`LevyStochCalc/Brownian/SimplePredictableRefineAppend`](https://prove2.me/theorems/78210238-573d-4711-bb11-ff9b0a1a12de), [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb).
--
--   Previous: [`SimplePredictable.sum_xi_mul_simpleIntegral_sub`](https://prove2.me/theorems/dfbfbaef-e395-42fa-a4db-142dc1f926ee) · Next: [`SimplePredictable.exists_mul_simple`](https://prove2.me/theorems/2d890f64-d894-41e2-b8b4-bc4a0edaf483).
--
--   [Source excerpt, lines 231–234](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraProduct.lean#L231-L234) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraProduct.lean#L230-L247 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraProduct`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.appendInterval_integralAgainst`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.appendInterval_integralAgainst_readable
    {T : ℝ} (G : SimplePredictable Ω T) {T' : ℝ}
    (hlt : G.partition (Fin.last G.N) < T') (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (G.appendInterval hlt).integralAgainst M t ω = G.integralAgainst M t ω := by sorry
