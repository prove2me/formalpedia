-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_smooth_compact_translate_majorant_408915f
-- name    : FunctionalInequalities.Analysis.exists_smooth_compact_translate_majorant_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:17:52.213267+00:00
-- url     : https://prove2.me/theorems/49797b62-cdd6-4c1a-9417-e769cf93779a
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
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Translation.lean#L10-L78 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Translation`, declaration `FunctionalInequalities.Analysis.exists_smooth_compact_translate_majorant`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Set
open scoped Topology ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.exists_smooth_compact_translate_majorant_408915f {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ η : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x) ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x,
        (χ (x + t • v)) ^ 2 * Real.exp (u x) ≤ η x := by sorry
