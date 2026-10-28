-- Prove2me | Theorems.Thm_MeasureTheory_holder_step_truncated_readable
-- name    : MeasureTheory.holder_step_truncated_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:59.201539+00:00
-- url     : https://prove2.me/theorems/f00a2353-058c-42b6-ba1e-aa2cf1b3b4c6
-- title:
--   Truncated Hölder Maximal Bound
-- statement:
--   This auxiliary lemma gives a Hölder estimate for the truncated running maximum.
--
--   Let $f$ be a nonnegative submartingale under a finite measure, let $p>1$, fix $n\in\mathbb N$, and let $K>0$. Then
--
--   $$
--   \int \big(\min(f_n^\ast,K)\big)^p\,d\mu
--   \leq
--   \frac{p}{p-1}
--   \left(\int f_n^p\,d\mu\right)^{1/p}
--   \left(\int \big(\min(f_n^\ast,K)\big)^p\,d\mu\right)^{(p-1)/p}.
--   $$
--
--   The integrals are represented as `ENNReal` lower integrals of `ENNReal.ofReal` powers.
--
--   This is the finite-truncation estimate used before taking a monotone supremum over $K$.
--
--   **Original Lean declaration header**
--
--   Within namespace `MeasureTheory`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma holder_step_truncated
--       [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
--       (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
--       (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
--       (∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ)
--         ≤ ENNReal.ofReal (p / (p - 1)) *
--             (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
--             (∫⁻ ω, ENNReal.ofReal ((min (runMax f n ω) K) ^ p) ∂μ) ^ ((p - 1) / p)
--   ```
--
--   **Module navigation**
--
--   Module: [`MathFin/Foundations/DoobLpMaximalInequality`](https://prove2.me/theorems/246417cb-a393-4700-8546-3a2d7f728869).
--
--   Supporting theorems: [`A_K_le_layer_integral`](https://prove2.me/theorems/3605b7cf-82c6-4d1c-9553-8a7bb463ed50), [`fubini_swap_truncated`](https://prove2.me/theorems/d6dd1ec2-dc45-4bb7-acdd-bd178c7f7911).
--
--   Previous: [`A_K_le_layer_integral`](https://prove2.me/theorems/3605b7cf-82c6-4d1c-9553-8a7bb463ed50) · Next: [`holder_step`](https://prove2.me/theorems/a6c79680-7ffa-4ec5-b28a-2e9350b5db77).
--
--   [Source excerpt, lines 652–659](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/MathFin/MathFin/Foundations/DoobLpMaximalInequality.lean#L652-L659) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L651-L753 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `_private.MathFin.Foundations.DoobLpMaximalInequality.0.MeasureTheory.holder_step_truncated`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_MathFin_Foundations_DoobLpMaximalInequality

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {Ω : Type*}
variable [m0 : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

lemma MeasureTheory.holder_step_truncated_readable
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    (∫⁻ ω, ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ p) ∂μ)
      ≤ ENNReal.ofReal (p / (p - 1)) *
          (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ p) ∂μ) ^ ((p - 1) / p) := by sorry
