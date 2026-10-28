-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_mul_eq_zero_of_tendsto_eLpNorm_readable
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_eq_zero_of_tendsto_eLpNorm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:50.940035+00:00
-- url     : https://prove2.me/theorems/9e82e98b-0377-41ae-b977-70c8c0709ea7
-- title:
--   Vanishing Pairings Under L² Convergence
-- statement:
--   This is the continuity of the $L^2$ pairing under convergence in extended $L^2$ norm.
--
--   Let $u,v:\Omega\to\mathbb R$ and let $u_n,v_n$ be sequences. Assume $u,v,u_n,v_n$ belong to $L^2(P)$, that
--   $$
--   \int u_nv_n\,dP=0\quad\text{for every }n,
--   $$
--   and that $u_n\to u$ and $v_n\to v$ in the sense that
--   $$
--   \operatorname{eLpNorm}(u_n-u,2,P)\to0,
--   \qquad
--   \operatorname{eLpNorm}(v_n-v,2,P)\to0.
--   $$
--   Then
--   $$
--   \int uv\,dP=0.
--   $$
--
--   This auxiliary functional-analytic statement transfers orthogonality from approximating sequences to their $L^2$ limits.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_eq_zero_of_tendsto_eLpNorm {u v : Ω → ℝ} {un vn : ℕ → Ω → ℝ}
--       (hu : MemLp u 2 P) (hv : MemLp v 2 P)
--       (hun : ∀ n, MemLp (un n) 2 P) (hvn : ∀ n, MemLp (vn n) 2 P)
--       (h0 : ∀ n, ∫ ω, un n ω * vn n ω ∂P = 0)
--       (hcu : Filter.Tendsto (fun n => eLpNorm (fun ω => un n ω - u ω) 2 P) Filter.atTop (nhds 0))
--       (hcv : Filter.Tendsto (fun n => eLpNorm (fun ω => vn n ω - v ω) 2 P) Filter.atTop (nhds 0)) :
--       ∫ ω, u ω * v ω ∂P = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossOrthogonalityLimit`](https://prove2.me/theorems/0a6cdcb3-be60-427a-8dc0-4862ed142b74).
--
--   Previous: [`memLp_simpleIntegral`](https://prove2.me/theorems/7c5f50d8-edb5-487c-a4bf-6c19ad9a378c) · Next: [`integral_stochasticIntegral_mul_eq_zero`](https://prove2.me/theorems/a9eee61c-6570-4194-86d3-3b8045d9de2c).
--
--   [Source excerpt, lines 332–338](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L332-L338) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L329-L368 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossOrthogonalityLimit`, declaration `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_eq_zero_of_tendsto_eLpNorm`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_eq_zero_of_tendsto_eLpNorm_readable {u v : Ω → ℝ} {un vn : ℕ → Ω → ℝ}
    (hu : MemLp u 2 P) (hv : MemLp v 2 P)
    (hun : ∀ n, MemLp (un n) 2 P) (hvn : ∀ n, MemLp (vn n) 2 P)
    (h0 : ∀ n, ∫ ω, un n ω * vn n ω ∂P = 0)
    (hcu : Filter.Tendsto (fun n => eLpNorm (fun ω => un n ω - u ω) 2 P) Filter.atTop (nhds 0))
    (hcv : Filter.Tendsto (fun n => eLpNorm (fun ω => vn n ω - v ω) 2 P) Filter.atTop (nhds 0)) :
    ∫ ω, u ω * v ω ∂P = 0 := by sorry
