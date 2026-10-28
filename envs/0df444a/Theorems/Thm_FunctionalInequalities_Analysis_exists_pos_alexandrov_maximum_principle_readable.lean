-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_pos_alexandrov_maximum_principle_readable
-- name    : FunctionalInequalities.Analysis.exists_pos_alexandrov_maximum_principle_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:46.078441+00:00
-- url     : https://prove2.me/theorems/fb6f8a3c-985d-4638-9d88-5993fe585328
-- title:
--   Alexandrov Maximum Principle
-- statement:
--   This formalizes the Alexandrov maximum principle, cited as Theorem 1.4.2 in Gutiérrez's treatment of the Monge–Ampère equation.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with measurable and Borel structures, and write $n=\dim E$. There exists $c>0$, depending only on $E$, such that for every convex $u:E\to\mathbb R$, every bounded open convex $\Omega$, and every $x_0\in\Omega$ with $u(x_0)<0$ and $u\ge0$ on $\partial\Omega$,
--
--   $$
--   \operatorname{ofReal}\!\left(c(-u(x_0))^n\right)
--   \le
--   \operatorname{vol}(\operatorname{subgradientImage}(u,\Omega))\,\operatorname{ofReal}\!\left(\operatorname{diam}(\Omega)^{n-1}\operatorname{infDist}(x_0,\partial\Omega)\right).
--   $$
--
--   The volume is an `ENNReal` value and the real factors are embedded with `ofReal`. The declaration is `exists_pos_alexandrov_maximum_principle_readable`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_pos_alexandrov_maximum_principle [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
--       [BorelSpace E] :
--       ∃ c : ℝ, 0 < c ∧ ∀ (u : E → ℝ), ConvexOn ℝ univ u → ∀ (Ω : Set E), IsOpen Ω → Convex ℝ Ω →
--         Bornology.IsBounded Ω → (∀ x ∈ frontier Ω, 0 ≤ u x) → ∀ x₀ ∈ Ω, u x₀ < 0 →
--         ENNReal.ofReal (c * (-u x₀) ^ Module.finrank ℝ E) ≤
--           (volume : Measure E) (subgradientImage u Ω) *
--             ENNReal.ofReal (diam Ω ^ (Module.finrank ℝ E - 1) * infDist x₀ (frontier Ω))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`exists_pos_volume_convexHull_closedBall_union_singleton_ge`](https://prove2.me/theorems/04941f10-f990-4b5d-a225-77ccc909d39f), [`exists_unit_inner_le_infDist_frontier`](https://prove2.me/theorems/f4f9ef6d-abf7-4073-89c1-856846d679e9), [`mem_subgradientImage_of_affine_le_of_nonneg_frontier`](https://prove2.me/theorems/f79e9028-f752-4900-ae74-36d3b8229978).
--
--   Previous: [`exists_pos_volume_convexHull_closedBall_union_singleton_ge`](https://prove2.me/theorems/04941f10-f990-4b5d-a225-77ccc909d39f) · Next: [`quadraticAt_subgradient_iff`](https://prove2.me/theorems/30c05a45-559f-4ce4-9d75-9148915945b6).
--
--   [Source excerpt, lines 1220–1226](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1220-L1226) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1216-L1397 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.exists_pos_alexandrov_maximum_principle`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open MeasureTheory Set Metric
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.exists_pos_alexandrov_maximum_principle_readable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : E → ℝ), ConvexOn ℝ univ u → ∀ (Ω : Set E), IsOpen Ω → Convex ℝ Ω →
      Bornology.IsBounded Ω → (∀ x ∈ frontier Ω, 0 ≤ u x) → ∀ x₀ ∈ Ω, u x₀ < 0 →
      ENNReal.ofReal (c * (-u x₀) ^ Module.finrank ℝ E) ≤
        (volume : Measure E) (subgradientImage u Ω) *
          ENNReal.ofReal (diam Ω ^ (Module.finrank ℝ E - 1) * infDist x₀ (frontier Ω)) := by sorry
