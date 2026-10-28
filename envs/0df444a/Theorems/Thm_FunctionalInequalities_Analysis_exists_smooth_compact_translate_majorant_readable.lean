-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_smooth_compact_translate_majorant_readable
-- name    : FunctionalInequalities.Analysis.exists_smooth_compact_translate_majorant_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:06.116978+00:00
-- url     : https://prove2.me/theorems/5a6cfef8-0f99-4ac1-ab61-4c7439b31f8f
-- title:
--   Smooth Compact Majorant for Small Translates
-- statement:
--   This formalizes a partial auxiliary statement related to Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $u,\chi:\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))\to\mathbb R$ be continuous, assume that $\chi$ has compact support, and fix $v$ in the Euclidean space. Then there exists a function $\eta$ such that:
--
--   1. $\eta$ is $C^\infty$ and compactly supported;
--   2. $\eta(x)\ge0$ for every $x$;
--   3. for every $t\in\mathbb R$ with $|t|\le1$ and every $x$,
--   $$\chi(x+tv)^2e^{u(x)}\le\eta(x).$$
--
--   This supplies a single smooth compactly supported majorant for all small translates of the cutoff. It does not assert any Hessian-energy estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_smooth_compact_translate_majorant {n : ℕ}
--       {u χ : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : Continuous u) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
--       (v : EuclideanSpace ℝ (Fin n)) :
--       ∃ η : EuclideanSpace ℝ (Fin n) → ℝ,
--         ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x) ∧
--         ∀ t : ℝ, |t| ≤ 1 → ∀ x,
--           (χ (x + t • v)) ^ 2 * Real.exp (u x) ≤ η x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Cutoff/Translation`](https://prove2.me/theorems/7e49ee02-1556-4ccf-9755-78f397c2f933).
--
--   [Source excerpt, lines 14–21](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Cutoff/Translation.lean#L14-L21) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Translation.lean#L10-L78 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Translation`, declaration `FunctionalInequalities.Analysis.exists_smooth_compact_translate_majorant`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Translation

open scoped Topology ContDiff

theorem FunctionalInequalities.Analysis.exists_smooth_compact_translate_majorant_readable {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ η : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x) ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x,
        (χ (x + t • v)) ^ 2 * Real.exp (u x) ≤ η x := by sorry
