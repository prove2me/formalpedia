-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_lintegral_sq_frozen_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_frozen_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:16.115647+00:00
-- url     : https://prove2.me/theorems/9644b3b1-54f1-4a8b-9c01-eff516b61ba6
-- title:
--   Squared Error of a Frozen Lipschitz Weight
-- statement:
--   This is an $L^2$ bound for freezing a Lipschitz function along a uniform grid.
--
--   Let $(\Omega,\mathcal F,P)$, the multidimensional Brownian motion $W$, its coordinate filtrations, the integrands $H_{mk}$, and the vector Itô-process version $X$ satisfy the hypotheses of `IsVectorItoVersion`. Assume $C\ge0$, $|H_{mk}(\omega,s)|\le C$, the drifts are measurable, $B\ge0$, and $|b_m(\omega,s)|\le B$. Let $\varphi:(\operatorname{Fin}(n)\to\mathbb R)\to\mathbb R$ satisfy $L\ge0$ and
--   $$
--   |\varphi(x)-\varphi(y)|\le L\|x-y\|
--   $$
--   for all $x,y$. Let $T>0$, $m\ne0$, and let $\xi_i$ be measurable, uniformly bounded random variables satisfying
--   $$
--   \xi_i(\omega)=\varphi\bigl(X_{t_i}(\omega)\bigr),\qquad t_i=\operatorname{unifGrid}(T,m,i).
--   $$
--   Then the frozen step process from `SimplePredictable.ofUnifGrid` satisfies
--   $$
--   \int_\Omega\int_{[0,T]}
--   \left\|\xi_{\mathrm{step}}(s,\omega)-\varphi(X_s(\omega))\right\|^2\,ds\,dP(\omega)
--   \le \operatorname{ofReal}(L^2)\,\operatorname{ofReal}\!\left(Tn\left(2\left(B\frac{T}{m}\right)^2+2d^2C^2\frac{T}{m}\right)\right).
--   $$
--
--   This is the principal approximation estimate for frozen weights in the martingale Riemann-sum construction.
--
--   **Formalization Note** The displayed double integral is an `ENNReal` integral, and the integrand is represented through the nonnegative norm coercion. The grid and step process are `unifGrid` and `SimplePredictable.ofUnifGrid`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsVectorItoVersion.lintegral_sq_frozen_sub_le
--       (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
--       (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
--       (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
--       {φ : (Fin n → ℝ) → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
--       (hφlip : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ L * ‖x - y‖)
--       {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
--       (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
--       (hmeas : ∀ i : Fin m, Measurable (ξ i))
--       (hξ : ∀ (i : Fin m) (ω : Ω), ξ i ω = φ (X (unifGrid T m (i : ℕ)) ω)) :
--       ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--           (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
--             - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
--         ≤ ENNReal.ofReal (L ^ 2)
--           * ENNReal.ofReal (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
--             + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoMartingaleRiemann`](https://prove2.me/theorems/a66fc89f-aa33-4950-8eab-8f30c14892aa).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`IsVectorItoVersion.lintegral_window_sq_norm_sub_le`](https://prove2.me/theorems/5ba0ca81-961e-4cc6-88d2-8048c9dcf930), [`exists_unifGrid_cell`](https://prove2.me/theorems/6498e1ec-297e-4445-a8b4-20374c8bb9d6).
--
--   Next: [`IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le`](https://prove2.me/theorems/74d597a9-d0f7-4590-b8a5-d44291007272).
--
--   [Source excerpt, lines 53–68](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoMartingaleRiemann.lean#L53-L68) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoMartingaleRiemann.lean#L49-L154 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoMartingaleRiemann`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_frozen_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoMartingaleRiemann

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoMartingaleRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
include hC0 hCH

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_frozen_sub_le_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {φ : (Fin n → ℝ) → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hφlip : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hξ : ∀ (i : Fin m) (ω : Ω), ξ i ω = φ (X (unifGrid T m (i : ℕ)) ω)) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))) := by sorry
