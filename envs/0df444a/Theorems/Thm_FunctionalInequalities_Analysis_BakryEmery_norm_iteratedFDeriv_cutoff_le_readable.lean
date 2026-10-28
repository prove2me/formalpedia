-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_iteratedFDeriv_cutoff_le_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_cutoff_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:03.607919+00:00
-- url     : https://prove2.me/theorems/d1de012f-6a55-4617-aaf5-23eabb181c3e
-- title:
--   Uniform Derivative Bounds for Cutoffs
-- statement:
--   This technical lemma gives uniform bounds for every fixed derivative order of the scaled cutoff.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $n\in\mathbb N$. There exists $C\in\mathbb R$ such that for every $R\ge1$ and every $x\in E$,
--
--   $$\left\|D^n\operatorname{cutoff}(R)(x)\right\|\le C.$$
--
--   The constant depends on $n$ and $E$ but is independent of $R\ge1$ and $x$. This estimate supports cutoff approximation arguments for functions of polynomial growth.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_iteratedFDeriv_cutoff_le (n : ℕ) :
--       ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ x : E, ‖iteratedFDeriv ℝ n (cutoff R) x‖ ≤ C
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/Temperate`](https://prove2.me/theorems/2dcac3f7-3919-472b-8b13-591e955577ca).
--
--   Previous: [`cutoff_eq_one`](https://prove2.me/theorems/85395b56-b174-481f-86b1-0d68ab4624ec) · Next: [`abs_laplacian_le`](https://prove2.me/theorems/f6e58a8e-3f46-421d-a064-a1f1705fd429).
--
--   [Source excerpt, lines 108–109](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L108-L109) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L106-L166 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_cutoff_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_cutoff_le_readable (n : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ x : E, ‖iteratedFDeriv ℝ n (cutoff R) x‖ ≤ C := by sorry
