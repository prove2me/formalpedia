-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_eq_add_of_sq_distances_readable
-- name    : LevyStochCalc.Brownian.Ito.ae_eq_add_of_sq_distances_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:12.992826+00:00
-- url     : https://prove2.me/theorems/99e33505-e2ff-46c1-a724-6a8f67657125
-- title:
--   Parallelogram Distance Criterion for Almost-Everywhere Additivity
-- statement:
--   This vendored statement gives an $L^2$ parallelogram criterion for identifying a sum almost everywhere.
--
--   Let $(\Omega,P)$ be a measurable space with measure $P$, and let $u,v,w:\Omega\to\mathbb R$ belong to $L^2(P)$. Let $A,B,C,D\in[0,\infty]$ be `ENNReal` values, all strictly below $\infty$. Assume that the squared $L^2$ quantities satisfy
--
--   $$
--   \int\|u\|_e^2\,dP=A,\qquad
--   \int\|v\|_e^2\,dP=B,\qquad
--   \int\|w\|_e^2\,dP=C,
--   $$
--
--   $$
--   \int\|w-u\|_e^2\,dP=B,\qquad
--   \int\|w-v\|_e^2\,dP=A,\qquad
--   \int\|u-v\|_e^2\,dP=D,
--   $$
--
--   and
--
--   $$
--   C+D=2A+2B.
--   $$
--
--   Then
--
--   $$
--   w(\omega)=u(\omega)+v(\omega)
--   $$
--
--   for $P$-almost every $\omega$. The statement explicitly uses the finiteness hypotheses to apply `toReal` to the `ENNReal` energy identities. This is an auxiliary uniqueness lemma for $L^2$ Itô-integral additivity.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_eq_add_of_sq_distances {u v w : Ω → ℝ}
--       (hu : MemLp u 2 P) (hv : MemLp v 2 P) (hw : MemLp w 2 P) {A B C D : ℝ≥0∞}
--       (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hC : C ≠ ⊤) (hD : D ≠ ⊤)
--       (hSu : ∫⁻ ω, (‖u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = A)
--       (hSv : ∫⁻ ω, (‖v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = B)
--       (hSw : ∫⁻ ω, (‖w ω‖₊ : ℝ≥0∞) ^ 2 ∂P = C)
--       (hSwu : ∫⁻ ω, (‖w ω - u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = B)
--       (hSwv : ∫⁻ ω, (‖w ω - v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = A)
--       (hSuv : ∫⁻ ω, (‖u ω - v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = D)
--       (hpar : C + D = 2 * A + 2 * B) :
--       w =ᵐ[P] fun ω => u ω + v ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoLinear`](https://prove2.me/theorems/0a2c3dbb-5791-49a2-875b-20068ab8311a).
--
--   Previous: [`lintegral_energy_const_mul`](https://prove2.me/theorems/ce857bc0-8f4c-4f64-b3bd-5184a06ec375) · Next: [`stochasticIntegralBrownian_add`](https://prove2.me/theorems/63f87c77-88d3-49b3-b12f-0856c509d6a6).
--
--   [Source excerpt, lines 187–197](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLinear.lean#L187-L197) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLinear.lean#L183-L246 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoLinear`, declaration `LevyStochCalc.Brownian.Ito.ae_eq_add_of_sq_distances`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.ae_eq_add_of_sq_distances_readable {u v w : Ω → ℝ}
    (hu : MemLp u 2 P) (hv : MemLp v 2 P) (hw : MemLp w 2 P) {A B C D : ℝ≥0∞}
    (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hC : C ≠ ⊤) (hD : D ≠ ⊤)
    (hSu : ∫⁻ ω, (‖u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = A)
    (hSv : ∫⁻ ω, (‖v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = B)
    (hSw : ∫⁻ ω, (‖w ω‖₊ : ℝ≥0∞) ^ 2 ∂P = C)
    (hSwu : ∫⁻ ω, (‖w ω - u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = B)
    (hSwv : ∫⁻ ω, (‖w ω - v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = A)
    (hSuv : ∫⁻ ω, (‖u ω - v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = D)
    (hpar : C + D = 2 * A + 2 * B) :
    w =ᵐ[P] fun ω => u ω + v ω := by sorry
