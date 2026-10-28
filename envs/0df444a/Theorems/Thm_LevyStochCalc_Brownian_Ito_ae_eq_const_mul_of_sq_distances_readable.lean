-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_eq_const_mul_of_sq_distances_readable
-- name    : LevyStochCalc.Brownian.Ito.ae_eq_const_mul_of_sq_distances_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:03.093513+00:00
-- url     : https://prove2.me/theorems/bfc53c08-9b3b-4e24-881f-cb00e6aeeb58
-- title:
--   Squared-Distance Characterization of a Scalar Multiple
-- statement:
--   This statement is an auxiliary Hilbert-space argument. Let $x,y:Ω→ℝ$ belong to `MemLp` with exponent $2$ under a measure $P$. Let $c∈ℝ$ and let $X,Y,Z∈[0,∞]$ be the squared `ENNReal` integrals of $x$, $y$, and $x-y$, respectively. Assume
--
--   1. $X=\int\|x\|^2dP$, $Y=\int\|y\|^2dP$, and $Z=\int\|x-y\|^2dP$;
--   2. $X.toReal=c^2Y.toReal$;
--   3. $Z.toReal=(c-1)^2Y.toReal$.
--
--   Then
--
--   $$x=c\,y\quad P\text{-almost everywhere}.$$
--
--   The result uses `toReal` on the `ENNReal` quantities and requires only the stated `MemLp` assumptions, not that $P$ be a probability measure. It is a reusable uniqueness criterion for identifying scalar multiples from squared distances.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_eq_const_mul_of_sq_distances {x y : Ω → ℝ} (hx : MemLp x 2 P) (hy : MemLp y 2 P)
--       {c : ℝ} {X Y Z : ℝ≥0∞}
--       (hSx : ∫⁻ ω, (‖x ω‖₊ : ℝ≥0∞) ^ 2 ∂P = X)
--       (hSy : ∫⁻ ω, (‖y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Y)
--       (hSxy : ∫⁻ ω, (‖x ω - y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Z)
--       (hXY : X.toReal = c ^ 2 * Y.toReal) (hZY : Z.toReal = (c - 1) ^ 2 * Y.toReal) :
--       x =ᵐ[P] fun ω => c * y ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoLinear`](https://prove2.me/theorems/0a2c3dbb-5791-49a2-875b-20068ab8311a).
--
--   Previous: [`stochasticIntegralBrownian_add`](https://prove2.me/theorems/63f87c77-88d3-49b3-b12f-0856c509d6a6) · Next: [`stochasticIntegralBrownian_const_mul`](https://prove2.me/theorems/ac110cf4-8674-43ad-ab92-f7fde08971b6).
--
--   [Source excerpt, lines 300–306](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLinear.lean#L300-L306) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLinear.lean#L298-L339 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoLinear`, declaration `LevyStochCalc.Brownian.Ito.ae_eq_const_mul_of_sq_distances`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLinear.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.ae_eq_const_mul_of_sq_distances_readable {x y : Ω → ℝ} (hx : MemLp x 2 P) (hy : MemLp y 2 P)
    {c : ℝ} {X Y Z : ℝ≥0∞}
    (hSx : ∫⁻ ω, (‖x ω‖₊ : ℝ≥0∞) ^ 2 ∂P = X)
    (hSy : ∫⁻ ω, (‖y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Y)
    (hSxy : ∫⁻ ω, (‖x ω - y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Z)
    (hXY : X.toReal = c ^ 2 * Y.toReal) (hZY : Z.toReal = (c - 1) ^ 2 * Y.toReal) :
    x =ᵐ[P] fun ω => c * y ω := by sorry
