-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_eq_of_contact_of_sublevel_bounds_readable
-- name    : FunctionalInequalities.Analysis.eq_of_contact_of_sublevel_bounds_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:59.432849+00:00
-- url     : https://prove2.me/theorems/5fba9dd0-6290-4810-ab52-5b74c100b270
-- title:
--   Sublevel Contact Uniqueness
-- statement:
--   This formalizes the Caffarelli contact-set lemma below a level.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with its Borel measurable structure, and let $u:E\to\mathbb R$ be convex. Fix $x_0,p\in E$ with
--   $$u(x_0)+\langle p,y-x_0\rangle\le u(y)\quad\text{for all }y\in E.$$
--   Let $R\in\mathbb R$. Assume that $\{y:u(y)\le R\}$ is compact and that every compact $Q\subseteq\{y:u(y)<R\}$ admits constants $a,b\in\mathbb R$ with $a>0$ and the two-sided bounds
--   $$\operatorname{ofReal}(a)\,\operatorname{vol}(G)\le\operatorname{vol}(\partial u(G))\le\operatorname{ofReal}(b)\,\operatorname{vol}(G)$$
--   for every open $G$ with $\overline G\subseteq Q$. Then every $y$ satisfying $u(y)<R$ and
--   $$u(y)=u(x_0)+\langle p,y-x_0\rangle$$
--   coincides with $x_0$:
--   $$y=x_0.$$
--
--   This is a reusable localized strict-convexity criterion; compactness is required only for the closed sublevel set, not for the full contact set.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem eq_of_contact_of_sublevel_bounds {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x₀ p : E}
--       (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y) {R : ℝ} (hK : IsCompact {y | u y ≤ R})
--       (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ {y | u y < R} → ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E,
--         IsOpen G → closure G ⊆ Q →
--         ENNReal.ofReal a * (volume : Measure E) G ≤ (volume : Measure E) (subgradientImage u G) ∧
--         (volume : Measure E) (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G)
--       {y : E} (hyR : u y < R) (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`eq_of_two_contacts_below`](https://prove2.me/theorems/1bde12d1-3df1-4935-9ced-e218f57c79c3).
--
--   Previous: [`eq_of_two_contacts_below`](https://prove2.me/theorems/1bde12d1-3df1-4935-9ced-e218f57c79c3) · Next: [`strictConvexOn_of_map_gradient`](https://prove2.me/theorems/2ec0713b-027d-49b5-9ef0-008413f11729).
--
--   [Source excerpt, lines 1918–1924](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1918-L1924) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1913-L1965 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.eq_of_contact_of_sublevel_bounds`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.eq_of_contact_of_sublevel_bounds_readable {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y) {R : ℝ} (hK : IsCompact {y | u y ≤ R})
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ {y | u y < R} → ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E,
      IsOpen G → closure G ⊆ Q →
      ENNReal.ofReal a * (volume : Measure E) G ≤ (volume : Measure E) (subgradientImage u G) ∧
      (volume : Measure E) (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G)
    {y : E} (hyR : u y < R) (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀ := by sorry
