-- Prove2me | Theorems.Thm_MeasureTheory_A_K_le_layer_integral_readable
-- name    : MeasureTheory.A_K_le_layer_integral_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:00.715753+00:00
-- url     : https://prove2.me/theorems/3605b7cf-82c6-4d1c-9553-8a7bb463ed50
-- title:
--   Truncated Layer-Cake Bound
-- statement:
--   This auxiliary lemma bounds the truncated maximal moment.
--
--   Let $f$ be a nonnegative submartingale, let $p>1$, fix $n\in\mathbb N$, and let $K>0$. Writing $f_n^\ast$ for the running maximum, one has
--
--   $$
--   \int \big(\min(f_n^\ast,K)\big)^p\,d\mu
--   \leq
--   p\int_{(0,K]}t^{p-2}
--   \left(\int_{\{\omega:t\leq f_n^\ast(\omega)\}}f_n(\omega)\,d\mu\right)dt.
--   $$
--
--   The quantities are represented using `ENNReal.ofReal` and lower integrals.
--
--   This is the truncated layer-cake stage of the proof of the strong Doob inequality.
--
--   **Original Lean declaration header**
--
--   Within namespace `MeasureTheory`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma A_K_le_layer_integral
--       [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
--       (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
--       (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
--       ∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ
--         ≤ ENNReal.ofReal p *
--             ∫⁻ t in Set.Ioc (0:ℝ) K,
--               ENNReal.ofReal (t ^ (p - 2)) *
--                 ENNReal.ofReal (∫ ω in {ω | t ≤ runMax f n ω}, f n ω ∂μ)
--   ```
--
--   **Module navigation**
--
--   Module: [`MathFin/Foundations/DoobLpMaximalInequality`](https://prove2.me/theorems/246417cb-a393-4700-8546-3a2d7f728869).
--
--   Previous: [`fubini_swap_truncated`](https://prove2.me/theorems/d6dd1ec2-dc45-4bb7-acdd-bd178c7f7911) · Next: [`holder_step_truncated`](https://prove2.me/theorems/f00a2353-058c-42b6-ba1e-aa2cf1b3b4c6).
--
--   [Source excerpt, lines 566–574](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/MathFin/MathFin/Foundations/DoobLpMaximalInequality.lean#L566-L574) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L564-L649 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `_private.MathFin.Foundations.DoobLpMaximalInequality.0.MeasureTheory.A_K_le_layer_integral`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_MathFin_Foundations_DoobLpMaximalInequality

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {Ω : Type*}
variable [m0 : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

lemma MeasureTheory.A_K_le_layer_integral_readable
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    ∫⁻ ω, ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ p) ∂μ
      ≤ ENNReal.ofReal p *
          ∫⁻ t in Set.Ioc (0:ℝ) K,
            ENNReal.ofReal (t ^ (p - 2)) *
              ENNReal.ofReal (∫ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, f n ω ∂μ) := by sorry
