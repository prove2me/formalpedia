-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_eq_of_two_contacts_below_readable
-- name    : FunctionalInequalities.Analysis.eq_of_two_contacts_below_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:11.028092+00:00
-- url     : https://prove2.me/theorems/1bde12d1-3df1-4935-9ced-e218f57c79c3
-- title:
--   Two Below-Level Contacts Coincide
-- statement:
--   This is an auxiliary contact-point uniqueness lemma.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with its Borel measurable structure, and let $u:E\to\mathbb R$ be convex. Fix $x_0,p\in E$ and assume
--   $$u(x_0)+\langle p,x-x_0\rangle\le u(x)\quad\text{for all }x\in E.$$
--   Let $R\in\mathbb R$, assume $\{x:u(x)\le R\}$ is compact, and suppose that every compact $Q\subseteq\{x:u(x)<R\}$ admits two-sided `ENNReal` volume bounds for open $G$ with $\overline G\subseteq Q$:
--   $$\operatorname{ofReal}(a)\,\operatorname{vol}(G)\le\operatorname{vol}(\partial u(G))\le\operatorname{ofReal}(b)\,\operatorname{vol}(G),$$
--   with $a>0$. If $u(x_0)<R$, $u(y)<R$, and
--   $$u(y)=u(x_0)+\langle p,y-x_0\rangle,$$
--   then
--   $$y=x_0.$$
--
--   This technical lemma is used to turn strict exposure into uniqueness of contacts below a level.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma eq_of_two_contacts_below {u : E → ℝ}
--       (hconv : ConvexOn ℝ univ u) {x₀ p : E}
--       (hp : ∀ x, u x₀ + ⟪p, x - x₀⟫ ≤ u x) {R : ℝ}
--       (hK : IsCompact {x | u x ≤ R})
--       (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ {x | u x < R} →
--         ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → closure G ⊆ Q →
--           ENNReal.ofReal a * (volume : Measure E) G ≤
--             (volume : Measure E) (subgradientImage u G) ∧
--           (volume : Measure E) (subgradientImage u G) ≤
--             ENNReal.ofReal b * (volume : Measure E) G)
--       (hxR : u x₀ < R) {y : E} (hyR : u y < R)
--       (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`contactSet_eq_singleton_of_exposed_of_local_bounds`](https://prove2.me/theorems/b68b47d0-6adf-4db3-9250-a72ca18aaa5f), [`exists_exposed_contact_of_lt`](https://prove2.me/theorems/955fb26b-d452-446f-81e7-00212e58fa6b).
--
--   Previous: [`subgradientImage_truncatedConjugate_eq`](https://prove2.me/theorems/e685fa4c-013a-44d7-b25b-31318e3dcf54) · Next: [`eq_of_contact_of_sublevel_bounds`](https://prove2.me/theorems/5fba9dd0-6290-4810-ab52-5b74c100b270).
--
--   [Source excerpt, lines 1758–1769](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1758-L1769) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1758-L1911 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `_private.FunctionalInequalities.Analysis.Convex.Caffarelli.0.FunctionalInequalities.Analysis.eq_of_two_contacts_below`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma FunctionalInequalities.Analysis.eq_of_two_contacts_below_readable {u : E → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ x, u x₀ + ⟪p, x - x₀⟫ ≤ u x) {R : ℝ}
    (hK : IsCompact {x | u x ≤ R})
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ {x | u x < R} →
      ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → closure G ⊆ Q →
        ENNReal.ofReal a * (volume : Measure E) G ≤
          (volume : Measure E) (subgradientImage u G) ∧
        (volume : Measure E) (subgradientImage u G) ≤
          ENNReal.ofReal b * (volume : Measure E) G)
    (hxR : u x₀ < R) {y : E} (hyR : u y < R)
    (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀ := by sorry
