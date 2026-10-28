-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_hasWeakDerivAlong_of_forall_cutoff_readable
-- name    : FunctionalInequalities.Analysis.exists_hasWeakDerivAlong_of_forall_cutoff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:19.107551+00:00
-- url     : https://prove2.me/theorems/db832ddc-e6e0-4365-ace7-102695429d13
-- title:
--   Gluing Local Weak Derivatives From Compact Cutoffs
-- statement:
--   This is a generic gluing theorem for weak derivatives.
--
--   Let $E$ be a finite-dimensional real inner-product normed space with its Borel measurable structure, and let $f:E\to\mathbb R$. Assume:
--
--   1. for every compact set $S$, the restriction of $f$ to $S$ belongs to $L^2$ with respect to restricted volume;
--   2. for every $C^1$ compactly supported cutoff $\chi$, there is a globally $L^2$ function $g_\chi$ such that $\chi f$ has weak derivative $g_\chi$ along a fixed vector $v$.
--
--   Then there exists $g:E\to\mathbb R$ such that $g$ is a weak derivative of $f$ along $v$, and for every compact $S$, $g$ belongs to $L^2$ with respect to volume restricted to $S$.
--
--   The conclusion is local $L^2$ regularity of the derivative rather than global $L^2$ regularity. It provides a cutoff-gluing interface for weak derivative constructions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_hasWeakDerivAlong_of_forall_cutoff {E : Type*} [NormedAddCommGroup E]
--       [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       {f : E → ℝ} (hf : ∀ S : Set E, IsCompact S → MemLp f 2 ((volume : Measure E).restrict S)) (v : E)
--       (hloc : ∀ χ : E → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
--         ∃ g : E → ℝ, HasWeakDerivAlong (fun x => χ x * f x) g v ∧ MemLp g 2 (volume : Measure E)) :
--       ∃ g : E → ℝ, HasWeakDerivAlong f g v ∧
--         ∀ S : Set E, IsCompact S → MemLp g 2 ((volume : Measure E).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Approximation`](https://prove2.me/theorems/55bb7a47-4741-4de8-91f0-25080da6fa69).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`HasWeakDerivAlong.mul_contDiff`](https://prove2.me/theorems/2a566c7d-243e-41f1-be35-eae8ff92ebb5).
--
--   Next: [`exists_contDiff_compact_weak_deriv_approximation`](https://prove2.me/theorems/2972130c-74ad-41b7-aa1b-dec182289761).
--
--   [Source excerpt, lines 27–33](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean#L27-L33) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean#L24-L139 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Approximation`, declaration `FunctionalInequalities.Analysis.exists_hasWeakDerivAlong_of_forall_cutoff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Approximation

open MeasureTheory Set Filter Metric

theorem FunctionalInequalities.Analysis.exists_hasWeakDerivAlong_of_forall_cutoff_readable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : ∀ S : Set E, IsCompact S → MemLp f 2 ((volume : Measure E).restrict S)) (v : E)
    (hloc : ∀ χ : E → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
      ∃ g : E → ℝ, HasWeakDerivAlong (fun x => χ x * f x) g v ∧ MemLp g 2 (volume : Measure E)) :
    ∃ g : E → ℝ, HasWeakDerivAlong f g v ∧
      ∀ S : Set E, IsCompact S → MemLp g 2 ((volume : Measure E).restrict S) := by sorry
