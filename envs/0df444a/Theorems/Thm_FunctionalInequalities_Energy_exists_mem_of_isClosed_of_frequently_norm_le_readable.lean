-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_exists_mem_of_isClosed_of_frequently_norm_le_readable
-- name    : FunctionalInequalities.Energy.exists_mem_of_isClosed_of_frequently_norm_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:43.390177+00:00
-- url     : https://prove2.me/theorems/1b83220f-71fb-46f4-9e5b-6d66af812e52
-- title:
--   Closed-Subspace Selection With A Frequently Bounded Hilbert Component
-- statement:
--   This is a closed-subspace selection lemma in a product of normed spaces.
--
--   Let $X$ be a real normed space, let $H$ be a complete real Hilbert space, and let $G\subseteq X\times H$ be a closed real submodule. Suppose sequences $x_n\in X$ and $y_n\in H$ satisfy
--
--   1. $(x_n,y_n)\in G$ for every $n$;
--   2. $x_n\to x_0$;
--   3. for some real $L$, the inequality $\|y_n\|\le L$ holds frequently along $n\to\infty$.
--
--   Then there exists $y_0\in H$ such that
--
--   $$
--   (x_0,y_0)\in G,
--   \qquad
--   \|y_0\|\le L.
--   $$
--
--   The Lean declaration is `exists_mem_of_isClosed_of_frequently_norm_le_readable`. “Frequently” is the filter-theoretic condition along `atTop`, not an eventual bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_mem_of_isClosed_of_frequently_norm_le
--       {G : Submodule ℝ (X × H)} (hG : IsClosed (G : Set (X × H)))
--       {x : ℕ → X} {y : ℕ → H} (hxy : ∀ n, (x n, y n) ∈ G)
--       {x₀ : X} (hx : Tendsto x atTop (𝓝 x₀)) {L : ℝ} (hL : ∃ᶠ n in atTop, ‖y n‖ ≤ L) :
--       ∃ y₀ : H, (x₀, y₀) ∈ G ∧ ‖y₀‖ ≤ L
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Relaxation/LinearPMap`](https://prove2.me/theorems/2ed50aac-81dd-45da-b8c8-597e80695a44).
--
--   Next: [`sequentialRelaxation_ofLinearPMap_le`](https://prove2.me/theorems/2e69ddca-a539-4bb5-8778-3f0a7a70ba16).
--
--   [Source excerpt, lines 51–55](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean#L51-L55) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean#L47-L162 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.LinearPMap`, declaration `FunctionalInequalities.Energy.exists_mem_of_isClosed_of_frequently_norm_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LinearPMap

open Filter Topology Set
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem FunctionalInequalities.Energy.exists_mem_of_isClosed_of_frequently_norm_le_readable
    {G : Submodule ℝ (X × H)} (hG : IsClosed (G : Set (X × H)))
    {x : ℕ → X} {y : ℕ → H} (hxy : ∀ n, (x n, y n) ∈ G)
    {x₀ : X} (hx : Tendsto x atTop (𝓝 x₀)) {L : ℝ} (hL : ∃ᶠ n in atTop, ‖y n‖ ≤ L) :
    ∃ y₀ : H, (x₀, y₀) ∈ G ∧ ‖y₀‖ ≤ L := by sorry
