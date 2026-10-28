-- Prove2me | Theorems.Thm_MeasureTheory_inner_t_integral_readable
-- name    : MeasureTheory.inner_t_integral_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:56.280893+00:00
-- url     : https://prove2.me/theorems/3ddc797c-837a-4b85-8121-292fb503538b
-- title:
--   Layer-Cake Inner Integral Evaluation
-- statement:
--   This auxiliary lemma evaluates a pointwise extended-real integral.
--
--   Let $f_\ast\geq0$ and $p>1$. Then
--
--   $$
--   \int_{(0,\infty)} t^{p-2}\,\mathbf 1_{\{t\leq f_\ast\}}\,dt
--   =
--   \frac{f_\ast^{p-1}}{p-1},
--   $$
--
--   with both sides interpreted through `ENNReal.ofReal`.
--
--   The identity is the scalar integration step in the layer-cake proof of Doob's $L^p$ maximal inequality.
--
--   **Formalization Note.** The integral is an `ENNReal` lower integral over $(0,\infty)$, and the indicator is $\mathbf 1_{\{t\leq f_\ast\}}$.
--
--   **Original Lean declaration header**
--
--   Within namespace `MeasureTheory`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma inner_t_integral
--       {fstar p : ℝ} (hfstar : 0 ≤ fstar) (hp : 1 < p) :
--       ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
--           {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t
--         = ENNReal.ofReal (fstar ^ (p - 1) / (p - 1))
--   ```
--
--   **Module navigation**
--
--   Module: [`MathFin/Foundations/DoobLpMaximalInequality`](https://prove2.me/theorems/246417cb-a393-4700-8546-3a2d7f728869).
--
--   Next: [`fubini_swap`](https://prove2.me/theorems/44a8d562-86b4-4fc8-8ba6-8f6c932e07c0).
--
--   [Source excerpt, lines 142–146](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/MathFin/MathFin/Foundations/DoobLpMaximalInequality.lean#L142-L146) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L140-L187 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, declaration `_private.MathFin.Foundations.DoobLpMaximalInequality.0.MeasureTheory.inner_t_integral`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_MathFin_Foundations_DoobLpMaximalInequality

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open ProbabilityTheory ENNReal Filter Set Finset
variable {Ω : Type*}

lemma MeasureTheory.inner_t_integral_readable
    {fstar p : ℝ} (hfstar : 0 ≤ fstar) (hp : 1 < p) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t
      = ENNReal.ofReal (fstar ^ (p - 1) / (p - 1)) := by sorry
