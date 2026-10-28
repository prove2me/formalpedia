-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_exposed_contact_of_lt_readable
-- name    : FunctionalInequalities.Analysis.exists_exposed_contact_of_lt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:56.824078+00:00
-- url     : https://prove2.me/theorems/955fb26b-d452-446f-81e7-00212e58fa6b
-- title:
--   Strictly Exposed Contact Below a Level
-- statement:
--   This establishes the existence of a strictly exposed contact point below a prescribed level.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be convex. Let $x,p\in E$ satisfy
--   $$u(x)+\langle p,y-x\rangle\le u(y)\quad\text{for all }y\in E.$$
--   For $R\in\mathbb R$, assume $u(x)<R$ and that the sublevel set $\{y:u(y)\le R\}$ is compact. Then there exist $z,\theta\in E$ such that
--   $$u(z)=u(x)+\langle p,z-x\rangle,\qquad u(z)<R,$$
--   and every other contact point in the sublevel set is strictly separated:
--   $$u(y)=u(x)+\langle p,y-x\rangle\ \land\ u(y)\le R\ \land\ y\ne z
--   \ \Longrightarrow\ \langle y-z,\theta\rangle<0.$$
--
--   The result supplies an exposed point for later contact-set arguments; it does not assert uniqueness of all contacts without the additional local volume hypotheses.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_exposed_contact_of_lt {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x p : E}
--       (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) {R : ℝ} (hR : u x < R) (hK : IsCompact {y | u y ≤ R}) :
--       ∃ z θ : E, u z = u x + ⟪p, z - x⟫ ∧ u z < R ∧
--         ∀ y, u y = u x + ⟪p, y - x⟫ → u y ≤ R → y ≠ z → ⟪y - z, θ⟫ < 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Previous: [`subgradient_mem_interior_of_strictConvexOn`](https://prove2.me/theorems/a618a7d2-7d13-4aef-99ab-5b9c4a71d731) · Next: [`exists_truncatedConjugate_eq`](https://prove2.me/theorems/c5409e58-60c1-4780-bcb8-119d240430ab).
--
--   [Source excerpt, lines 1206–1209](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1206-L1209) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1202-L1260 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.exists_exposed_contact_of_lt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open scoped RealInnerProductSpace
open Set
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.exists_exposed_contact_of_lt_readable {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) {R : ℝ} (hR : u x < R) (hK : IsCompact {y | u y ≤ R}) :
    ∃ z θ : E, u z = u x + ⟪p, z - x⟫ ∧ u z < R ∧
      ∀ y, u y = u x + ⟪p, y - x⟫ → u y ≤ R → y ≠ z → ⟪y - z, θ⟫ < 0 := by sorry
