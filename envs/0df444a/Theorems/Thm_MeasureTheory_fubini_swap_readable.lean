-- Prove2me | Theorems.Thm_MeasureTheory_fubini_swap_readable
-- name    : MeasureTheory.fubini_swap_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:54.719543+00:00
-- url     : https://prove2.me/theorems/44a8d562-86b4-4fc8-8ba6-8f6c932e07c0
-- title:
--   Fubini Swap for the Maximal Layer Integral
-- statement:
--   This auxiliary lemma performs the Fubini step for a nonnegative submartingale.
--
--   Let $f:\mathbb N\times\Omega\to\mathbb R$ be a nonnegative submartingale with respect to a filtration $\mathcal G$ and a finite measure $\mu$, let $p>1$, and fix $n\in\mathbb N$. Then
--
--   $$
--   \int_{(0,\infty)} t^{p-2}\int_{\{\,\omega:t\leq f_n^\ast(\omega)\}}f_n(\omega)\,d\mu\,dt
--   =
--   \int_\Omega f_n(\omega)\frac{(f_n^\ast(\omega))^{p-1}}{p-1}\,d\mu,
--   $$
--
--   where $f_n^\ast$ is the discrete running maximum.
--
--   This is a technical Fubini identity used in the strong Doob $L^p$ estimate.
--
--   **Formalization Note.** The displayed integrals are represented as `ENNReal` lower integrals with `ofReal` coercions.
--
--   **Original Lean declaration header**
--
--   Within namespace `MeasureTheory`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma fubini_swap
--       [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
--       (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
--       (hp : 1 < p) (n : ℕ) :
--       ∫⁻ t in Set.Ioi (0:ℝ),
--           ENNReal.ofReal (t ^ (p - 2)) *
--             ∫⁻ ω in {ω | t ≤ runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
--         = ∫⁻ ω, ENNReal.ofReal (f n ω) *
--                 ENNReal.ofReal ((runMax f n ω) ^ (p - 1) / (p - 1)) ∂μ
--   ```
--
--   **Module navigation**
--
--   Module: [`MathFin/Foundations/DoobLpMaximalInequality`](https://prove2.me/theorems/246417cb-a393-4700-8546-3a2d7f728869).
--
--   Supporting theorems: [`inner_t_integral`](https://prove2.me/theorems/3ddc797c-837a-4b85-8121-292fb503538b).
--
--   Previous: [`inner_t_integral`](https://prove2.me/theorems/3ddc797c-837a-4b85-8121-292fb503538b) · Next: [`fubini_swap_truncated`](https://prove2.me/theorems/d6dd1ec2-dc45-4bb7-acdd-bd178c7f7911).
--
--   [Source excerpt, lines 201–209](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/MathFin/MathFin/Foundations/DoobLpMaximalInequality.lean#L201-L209) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L189-L339 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `_private.MathFin.Foundations.DoobLpMaximalInequality.0.MeasureTheory.fubini_swap`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_MathFin_Foundations_DoobLpMaximalInequality

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
variable {Ω : Type*}
variable [m0 : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

lemma MeasureTheory.fubini_swap_readable
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1) / (p - 1)) ∂μ := by sorry
