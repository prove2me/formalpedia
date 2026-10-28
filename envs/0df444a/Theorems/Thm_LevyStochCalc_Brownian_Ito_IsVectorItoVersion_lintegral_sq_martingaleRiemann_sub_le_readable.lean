-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_lintegral_sq_martingaleRiemann_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:08.189992+00:00
-- url     : https://prove2.me/theorems/74d597a9-d0f7-4590-b8a5-d44291007272
-- title:
--   Squared Error of a Martingale Riemann Sum
-- statement:
--   This is an $L^2$ error estimate for a martingale Riemann sum along a vector Itô process.
--
--   Let $(\Omega,\mathcal F,P)$, the $d$-dimensional Brownian motion, its coordinate filtrations, the integrands $H_{pk}$, and the vector Itô-process version $X$ satisfy the stated measurability, progressive measurability, finite squared-integral, and `IsVectorItoVersion` hypotheses. Assume $C\ge0$, $|H_{pk}|\le C$, measurable drifts bounded by $B\ge0$, and let $\varphi$ satisfy $|\varphi(x)|\le K_\varphi$ and
--   $$
--   |\varphi(x)-\varphi(y)|\le L\|x-y\|,
--   \qquad L\ge0.
--   $$
--   Fix $k\in\operatorname{Fin}(d)$. Let $G$ be measurable and progressively measurable with finite squared extended integrals and $|G(\omega,s)|\le C_G$ for $C_G\ge0$. Assume also that $\varphi(X_s)G_s$ is measurable, progressively measurable, and has finite squared extended integrals. For $T>0$ and $m\ne0$, the frozen-weight sum satisfies
--   $$
--   \int_\Omega\left|\sum_{i<m}\varphi(X_{t_i})\bigl(I_G(t_{i+1})-I_G(t_i)\bigr)-I_{\varphi(X)G}(T)\right|^2dP
--   \le \operatorname{ofReal}(C_G^2)\operatorname{ofReal}(L^2)
--   \operatorname{ofReal}\!\left(Tn\left(2\left(B\frac{T}{m}\right)^2+2d^2C^2\frac{T}{m}\right)\right),
--   $$
--   where $t_i=\operatorname{unifGrid}(T,m,i)$.
--
--   This is the quantitative martingale Riemann-sum approximation used in the vector Itô formula.
--
--   **Formalization Note** The squared norm integral is an `ENNReal` integral. The boundedness of $\varphi$ is used as a hypothesis even though the conclusion is the displayed error bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le
--       (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
--       (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
--       (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
--       {φ : (Fin n → ℝ) → ℝ} {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
--       {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ L * ‖x - y‖)
--       (k : Fin d) {G : Ω → ℝ → ℝ} (hGm : Measurable (Function.uncurry G))
--       (hGp : Probability.ProgressivelyMeasurable ℱ G)
--       (hGs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {CG : ℝ} (hCG0 : 0 ≤ CG) (hCG : ∀ ω s, |G ω s| ≤ CG)
--       (hmg : Measurable (Function.uncurry fun ω s => φ (X s ω) * G ω s))
--       (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) * G ω s)
--       (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖φ (X s ω) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
--       ∫⁻ ω, (‖(∑ i : Fin m, φ (X (unifGrid T m (i : ℕ)) ω)
--             * (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
--                 (unifGrid T m ((i : ℕ) + 1)) ω
--               - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
--                 (unifGrid T m (i : ℕ)) ω))
--           - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
--               hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
--         ≤ ENNReal.ofReal (CG ^ 2) * (ENNReal.ofReal (L ^ 2)
--           * ENNReal.ofReal (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
--             + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoMartingaleRiemann`](https://prove2.me/theorems/a66fc89f-aa33-4950-8eab-8f30c14892aa).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`IsVectorItoVersion.lintegral_sq_frozen_sub_le`](https://prove2.me/theorems/9644b3b1-54f1-4a8b-9c01-eff516b61ba6), [`lintegral_sq_stochasticIntegral_mul_sub_le`](https://prove2.me/theorems/0931c8b0-f5be-481f-ade1-da8d876465a1), [`stochasticIntegralBrownian_integralAgainst`](https://prove2.me/theorems/ad605701-48f4-400c-83de-f35b5212c9ce).
--
--   Previous: [`IsVectorItoVersion.lintegral_sq_frozen_sub_le`](https://prove2.me/theorems/9644b3b1-54f1-4a8b-9c01-eff516b61ba6).
--
--   [Source excerpt, lines 161–186](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoMartingaleRiemann.lean#L161-L186) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoMartingaleRiemann.lean#L156-L228 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoMartingaleRiemann`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {φ : (Fin n → ℝ) → ℝ} {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ L * ‖x - y‖)
    (k : Fin d) {G : Ω → ℝ → ℝ} (hGm : Measurable (Function.uncurry G))
    (hGp : Probability.ProgressivelyMeasurable ℱ G)
    (hGs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {CG : ℝ} (hCG0 : 0 ≤ CG) (hCG : ∀ ω s, |G ω s| ≤ CG)
    (hmg : Measurable (Function.uncurry fun ω s => φ (X s ω) * G ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) * G ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖φ (X s ω) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∫⁻ ω, (‖(∑ i : Fin m, φ (X (unifGrid T m (i : ℕ)) ω)
          * (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (unifGrid T m (i : ℕ)) ω))
        - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (CG ^ 2) * (ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))) := by sorry
