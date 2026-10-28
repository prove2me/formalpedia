-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_compact_sections_subset_and_shrink_readable
-- name    : FunctionalInequalities.Analysis.exists_compact_sections_subset_and_shrink_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:49.53747+00:00
-- url     : https://prove2.me/theorems/e7f0ab2e-a85f-430a-8fd7-c28dea0e4a20
-- title:
--   Compactness and Shrinking of Exposed Sections
-- statement:
--   This formalizes the exposed-point section estimate used in the Caffarelli argument.
--
--   Let $E$ be finite-dimensional, let $u:E\to\mathbb R$ be convex, and let $x_0,p\in E$ satisfy
--
--   $$
--   u(x_0)+\langle p,y-x_0\rangle\le u(y)\quad\text{for all }y.
--   $$
--
--   Assume the contact set $C=\{x:u(x)=u(x_0)+\langle p,x-x_0\rangle\}$ is compact. Let $x_e\in C$, let $\|\theta\|=1$, assume $x_e$ is exposed in direction $\theta$, and let $h>0$. For
--
--   $$
--   S_\varepsilon=\{x:u(x)-u(x_0)-\langle p,x-x_0\rangle<\varepsilon(\langle x-x_e,\theta\rangle+h)\},
--   $$
--
--   there is a compact set $Q$ containing $S_\varepsilon$ for all sufficiently small positive $\varepsilon$. Moreover, for every $\delta>0$, sufficiently small positive $\varepsilon$ give
--
--   $$
--   S_\varepsilon\subseteq\operatorname{cthickening}_\delta\big(C\cap\{x:-h\le\langle x-x_e,\theta\rangle\}\big).
--   $$
--
--   The declaration is `exists_compact_sections_subset_and_shrink_readable`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_compact_sections_subset_and_shrink [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
--       {x₀ p : E} (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y)
--       (hC : IsCompact {x | u x = u x₀ + ⟪p, x - x₀⟫}) {xe θ : E}
--       (hxe : u xe = u x₀ + ⟪p, xe - x₀⟫) (hθ : ‖θ‖ = 1)
--       (hexp : ∀ x, u x = u x₀ + ⟪p, x - x₀⟫ → x ≠ xe → ⟪x - xe, θ⟫ < 0) {h : ℝ} (hh : 0 < h) :
--       (∃ Q : Set E, IsCompact Q ∧ ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
--         {x | u x - (u x₀ + ⟪p, x - x₀⟫) < ε * (⟪x - xe, θ⟫ + h)} ⊆ Q) ∧
--       ∀ δ > 0, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
--         {x | u x - (u x₀ + ⟪p, x - x₀⟫) < ε * (⟪x - xe, θ⟫ + h)} ⊆
--           cthickening δ ({x | u x = u x₀ + ⟪p, x - x₀⟫} ∩ {x | -h ≤ ⟪x - xe, θ⟫})
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Previous: [`infDist_frontier_image_le_of_width`](https://prove2.me/theorems/942275ce-7a7e-445b-9191-6b35e86c5433) · Next: [`contact_stepA`](https://prove2.me/theorems/8b79d3f8-eb05-43a8-ba70-26607440bbcb).
--
--   [Source excerpt, lines 181–190](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L181-L190) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L175-L344 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.exists_compact_sections_subset_and_shrink`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open Set Metric Filter
open scoped RealInnerProductSpace Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.exists_compact_sections_subset_and_shrink_readable [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {x₀ p : E} (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y)
    (hC : IsCompact {x | u x = u x₀ + ⟪p, x - x₀⟫}) {xe θ : E}
    (hxe : u xe = u x₀ + ⟪p, xe - x₀⟫) (hθ : ‖θ‖ = 1)
    (hexp : ∀ x, u x = u x₀ + ⟪p, x - x₀⟫ → x ≠ xe → ⟪x - xe, θ⟫ < 0) {h : ℝ} (hh : 0 < h) :
    (∃ Q : Set E, IsCompact Q ∧ ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      {x | u x - (u x₀ + ⟪p, x - x₀⟫) < ε * (⟪x - xe, θ⟫ + h)} ⊆ Q) ∧
    ∀ δ > 0, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
      {x | u x - (u x₀ + ⟪p, x - x₀⟫) < ε * (⟪x - xe, θ⟫ + h)} ⊆
        cthickening δ ({x | u x = u x₀ + ⟪p, x - x₀⟫} ∩ {x | -h ≤ ⟪x - xe, θ⟫}) := by sorry
