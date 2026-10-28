-- Prove2me | Theorems.Thm_MeasureTheory_runMax_pow_lintegral_lt_top_readable
-- name    : MeasureTheory.runMax_pow_lintegral_lt_top_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:59.007051+00:00
-- url     : https://prove2.me/theorems/421f4987-079a-483b-8873-a3f60d5b510d
-- title:
--   Finiteness of the Maximal $L^p$ Integral
-- statement:
--   This auxiliary lemma transfers finiteness from a submartingale terminal value to its running maximum.
--
--   Let $f$ be a nonnegative submartingale under a finite measure, let $p>1$, and fix $n\in\mathbb N$. If
--
--   $$
--   \int f_n^p\,d\mu<\infty,
--   $$
--
--   then
--
--   $$
--   \int (f_n^\ast)^p\,d\mu<\infty,
--   $$
--
--   where $f_n^\ast$ is the maximum of $f_k$ for $k\leq n$. The integrals are `ENNReal` lower integrals of `ENNReal.ofReal` powers.
--
--   This result supplies the finiteness needed to pass from truncated maximal estimates to the untruncated setting.
--
--   **Original Lean declaration header**
--
--   Within namespace `MeasureTheory`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma runMax_pow_lintegral_lt_top
--       [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
--       (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω) (hp : 1 < p) (n : ℕ)
--       (hB_lt_top : ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ < ⊤) :
--       ∫⁻ ω, ENNReal.ofReal ((runMax f n ω) ^ p) ∂μ < ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`MathFin/Foundations/DoobLpMaximalInequality`](https://prove2.me/theorems/246417cb-a393-4700-8546-3a2d7f728869).
--
--   Supporting theorems: [`holder_step_truncated`](https://prove2.me/theorems/f00a2353-058c-42b6-ba1e-aa2cf1b3b4c6).
--
--   Previous: [`holder_step`](https://prove2.me/theorems/a6c79680-7ffa-4ec5-b28a-2e9350b5db77) · Next: [`maximal_ineq_Lp`](https://prove2.me/theorems/3d6a746c-5b37-4dc6-83c9-71b26ca49833).
--
--   [Source excerpt, lines 844–848](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/MathFin/MathFin/Foundations/DoobLpMaximalInequality.lean#L844-L848) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L841-L925 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `_private.MathFin.Foundations.DoobLpMaximalInequality.0.MeasureTheory.runMax_pow_lintegral_lt_top`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_MathFin_Foundations_DoobLpMaximalInequality

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {Ω : Type*}
variable [m0 : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

lemma MeasureTheory.runMax_pow_lintegral_lt_top_readable
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω) (hp : 1 < p) (n : ℕ)
    (hB_lt_top : ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ < ⊤) :
    ∫⁻ ω, ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) ∂μ < ⊤ := by sorry
