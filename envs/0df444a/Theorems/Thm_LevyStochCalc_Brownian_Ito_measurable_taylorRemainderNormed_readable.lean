-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_measurable_taylorRemainderNormed_readable
-- name    : LevyStochCalc.Brownian.Ito.measurable_taylorRemainderNormed_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:25.286889+00:00
-- url     : https://prove2.me/theorems/82f77efa-c25f-4464-bcbe-e2c70b974c2c
-- title:
--   Measurability of the Normed Taylor Remainder
-- statement:
--   This is a measurability lemma for a second-order Taylor remainder.
--
--   Let $E$ be a second-countable normed real vector space with its Borel measurable structure. Let $f:E\to\mathbb R$, $f':E\to(E\to\mathbb R)$, and $f'':E\to(E\to(E\to\mathbb R))$ be continuous, with the derivative-valued maps interpreted as continuous linear maps. Let $x_i:\Omega\to E$ be measurable for every $i\in\mathbb N$. Then, for every $m\in\mathbb N$,
--   $$
--   \omega\longmapsto \operatorname{taylorRemainderNormed}(f,f',f'',(x_i(\omega))_{i\in\mathbb N},m)
--   $$
--   is measurable.
--
--   This technical result supplies measurability of the grid Taylor remainder used in vector Itô-formula estimates.
--
--   **Formalization Note** The exact derivative objects are Lean `ContinuousLinearMap`s, and the remainder is the definition `taylorRemainderNormed`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem measurable_taylorRemainderNormed {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
--       {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} (hfc : Continuous f) (hf'c : Continuous f')
--       (hf''c : Continuous f'') {x : ℕ → Ω → E} (hx : ∀ i, Measurable (x i)) (m : ℕ) :
--       Measurable fun ω => taylorRemainderNormed f f' f'' (fun i => x i ω) m
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoTaylor`](https://prove2.me/theorems/e2f63476-dcbb-4f48-b908-f9b176dad140).
--
--   Definition modules: [`LevyStochCalc/Brownian/TaylorTwoVector`](https://prove2.me/theorems/7b95962e-e11d-4fe9-a26b-01c2fa7c2715).
--
--   Next: [`sum_integral_sq_norm_vectorItoIncrement_le`](https://prove2.me/theorems/f8183882-c470-441e-b8d8-7efc9444036e).
--
--   [Source excerpt, lines 41–44](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoTaylor.lean#L41-L44) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoTaylor.lean#L39-L60 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoTaylor`, declaration `LevyStochCalc.Brownian.Ito.measurable_taylorRemainderNormed`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoTaylor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoTaylor.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem LevyStochCalc.Brownian.Ito.measurable_taylorRemainderNormed_readable {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} (hfc : Continuous f) (hf'c : Continuous f')
    (hf''c : Continuous f'') {x : ℕ → Ω → E} (hx : ∀ i, Measurable (x i)) (m : ℕ) :
    Measurable fun ω => taylorRemainderNormed f f' f'' (fun i => x i ω) m := by sorry
