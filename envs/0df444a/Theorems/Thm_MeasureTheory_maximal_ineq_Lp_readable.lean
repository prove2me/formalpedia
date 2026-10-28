-- Prove2me | Theorems.Thm_MeasureTheory_maximal_ineq_Lp_readable
-- name    : MeasureTheory.maximal_ineq_Lp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:57.460364+00:00
-- url     : https://prove2.me/theorems/3d6a746c-5b37-4dc6-83c9-71b26ca49833
-- title:
--   Doob’s Discrete-Time $L^p$ Maximal Inequality
-- statement:
--   This formalizes Doob’s strong-type maximal inequality for discrete-time submartingales.
--
--   Let $(\Omega,\mathcal F,\mu)$ be a finite measure space, let $\mathcal G$ be a filtration indexed by $\mathbb N$, let $f_n:\Omega\to\mathbb R$ be a $\mathcal G$-submartingale, and let $p\in\mathbb R$ satisfy $1<p$. Assume $f_n(\omega)\ge 0$ for every $n$ and $\omega$. For each $n$, define the running maximum $f_n^*(\omega)=\max_{0\le k\le n}f_k(\omega)$.
--
--   $$\|f_n^*\|_{L^p(\mu)}\le \frac{p}{p-1}\,\|f_n\|_{L^p(\mu)}.$$
--
--   The Lean statement uses `eLpNorm` with exponent `ENNReal.ofReal p`; thus both sides are values in $[0,\infty]$, and the running maximum is represented by a finite supremum. This is a reusable strong-type maximal estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `MeasureTheory`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem maximal_ineq_Lp
--       [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
--       (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
--       (hp : 1 < p) (n : ℕ) :
--       eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
--           (fun k ↦ f k ω)) (ENNReal.ofReal p) μ
--         ≤ ENNReal.ofReal (p / (p - 1)) *
--             eLpNorm (f n) (ENNReal.ofReal p) μ
--   ```
--
--   **Module navigation**
--
--   Module: [`MathFin/Foundations/DoobLpMaximalInequality`](https://prove2.me/theorems/246417cb-a393-4700-8546-3a2d7f728869).
--
--   Supporting theorems: [`holder_step`](https://prove2.me/theorems/a6c79680-7ffa-4ec5-b28a-2e9350b5db77), [`runMax_pow_lintegral_lt_top`](https://prove2.me/theorems/421f4987-079a-483b-8873-a3f60d5b510d).
--
--   Previous: [`runMax_pow_lintegral_lt_top`](https://prove2.me/theorems/421f4987-079a-483b-8873-a3f60d5b510d).
--
--   [Source excerpt, lines 939–946](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/MathFin/MathFin/Foundations/DoobLpMaximalInequality.lean#L939-L946) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L927-L984 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `MeasureTheory.maximal_ineq_Lp`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_MathFin_Foundations_DoobLpMaximalInequality

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {Ω : Type*}
variable [m0 : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

theorem MeasureTheory.maximal_ineq_Lp_readable
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ f k ω)) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) *
          eLpNorm (f n) (ENNReal.ofReal p) μ := by sorry
