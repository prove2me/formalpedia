-- Prove2me | Theorems.Thm_MongeKantorovichYao_duality_of_bounded
-- name    : MongeKantorovichYao.duality_of_bounded
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T20:52:48.355994+00:00
-- url     : https://prove2.me/theorems/77776d9e-7847-457e-b2d9-2ada821c3502
-- title:
--   Proposition 4.31 — duality for bounded continuous costs
-- statement:
--   Let $X,Y$ be Polish spaces with their Borel σ-algebras, $\mu$ and $\nu$ Borel probability measures on $X$ and $Y$, and $c : X\times Y\to[0,\infty)$ continuous and bounded. Then
--   $$\inf_{\pi\in\Pi(\mu,\nu)}\int_{X\times Y}c\,d\pi=\sup\Big\{\int_Y\varphi\,d\nu+\int_X\psi\,d\mu\Big\},$$
--   the supremum being over bounded continuous $\psi : X\to\mathbb R$ and $\varphi : Y\to\mathbb R$ with $\varphi(y)+\psi(x)\le c(x,y)$ for all $x,y$.
--
--   This is the version of duality proved in Section 4.4, with the extra assumption that $c$ is bounded.
--
--   **Formalization Note** Both sides are compared in the extended reals (they are in fact finite, lying in $[0,\sup c]$). Nonnegativity of $c$ is the standing assumption of Section 4.
-- source:
--   Colin Yao, *Monge–Kantorovich and Transportation Theory* (paper dated September 10, 2023), p. 16, Proposition 4.31 (proof pp. 17–18)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory

namespace MongeKantorovichYao

theorem duality_of_bounded {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : X × Y → ℝ) (hc_cont : Continuous c) (hc_nonneg : ∀ p, 0 ≤ c p)
    (hc_bdd : BddAbove (Set.range c)) :
    (⨅ π ∈ transferencePlans μ ν, ((∫ p, c p ∂π : ℝ) : EReal)) =
      ⨆ (ψ : BoundedContinuousFunction X ℝ) (φ : BoundedContinuousFunction Y ℝ)
        (_ : ∀ x y, ψ x + φ y ≤ c (x, y)),
        (((∫ x, ψ x ∂μ) + (∫ y, φ y ∂ν) : ℝ) : EReal) := by sorry

end MongeKantorovichYao
