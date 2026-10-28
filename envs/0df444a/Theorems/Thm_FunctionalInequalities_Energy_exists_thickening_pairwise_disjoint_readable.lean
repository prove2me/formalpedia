-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_exists_thickening_pairwise_disjoint_readable
-- name    : FunctionalInequalities.Energy.exists_thickening_pairwise_disjoint_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:57.377984+00:00
-- url     : https://prove2.me/theorems/b2a5cca9-524f-466c-8c07-05aff010b370
-- title:
--   Common Thickening Radius For Finitely Many Compact Sets
-- statement:
--   This is a metric separation lemma for finitely many pairwise disjoint compact sets.
--
--   Let $X$ be a metric space, let $N\in\mathbb N$, and let $K_i\subseteq X$ be compact for every $i\in\mathbb N$. Assume that distinct sets are pairwise disjoint:
--
--   $$
--    i\ne j\implies K_i\cap K_j=\varnothing.
--   $$
--
--   Then there exists a radius $\rho>0$ such that for all distinct $i,j<N$, the metric thickenings are disjoint:
--
--   $$
--   \operatorname{thickening}(\rho,K_i)\cap
--   \operatorname{thickening}(\rho,K_j)=\varnothing.
--   $$
--
--   The Lean declaration is `exists_thickening_pairwise_disjoint_readable`. Only the first $N$ indices are required to have disjoint thickenings; the conclusion makes no assertion about indices at or beyond $N$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_thickening_pairwise_disjoint (N : ℕ) (Kc : ℕ → Set X)
--       (hcomp : ∀ n, IsCompact (Kc n)) (hdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j)) :
--       ∃ ρ : ℝ, 0 < ρ ∧ ∀ i < N, ∀ j < N, i ≠ j →
--         Disjoint (Metric.thickening ρ (Kc i)) (Metric.thickening ρ (Kc j))
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Density`](https://prove2.me/theorems/5367291c-d0c5-48f5-b722-92a892987587).
--
--   Previous: [`lowerSemicontinuous_secant`](https://prove2.me/theorems/fd7d5e26-5f7d-4c26-af0b-4d2fd37844d8) · Next: [`exists_patch_of_isCompact`](https://prove2.me/theorems/ea72d420-aff6-4dac-9243-2603cf6d9d59).
--
--   [Source excerpt, lines 123–126](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L123-L126) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L121-L154 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Density`, declaration `FunctionalInequalities.Energy.exists_thickening_pairwise_disjoint`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density

variable {X : Type*} [MetricSpace X]

theorem FunctionalInequalities.Energy.exists_thickening_pairwise_disjoint_readable (N : ℕ) (Kc : ℕ → Set X)
    (hcomp : ∀ n, IsCompact (Kc n)) (hdisj : ∀ i j, i ≠ j → Disjoint (Kc i) (Kc j)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i < N, ∀ j < N, i ≠ j →
      Disjoint (Metric.thickening ρ (Kc i)) (Metric.thickening ρ (Kc j)) := by sorry
