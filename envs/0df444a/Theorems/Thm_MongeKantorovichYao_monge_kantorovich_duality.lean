-- Prove2me | Theorems.Thm_MongeKantorovichYao_monge_kantorovich_duality
-- name    : MongeKantorovichYao.monge_kantorovich_duality
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:31:45.441748+00:00
-- url     : https://prove2.me/theorems/a36283f0-e2ef-4556-aa95-2e391068f5ea
-- title:
--   Theorem 4.1 — Monge–Kantorovich duality
-- statement:
--   Let $X$ and $Y$ be Polish spaces equipped with their Borel σ-algebras, and let $\mu$ and $\nu$ be Borel probability measures on $X$ and $Y$. Let $c : X\times Y\to[0,\infty)$ be a continuous nonnegative cost function, and let $\Pi(\mu,\nu)$ be the set of transference plans (probability measures on $X\times Y$ with marginals $\mu$ and $\nu$). Then:
--
--   1. the Kantorovich problem has a minimizer: there is $\pi^\star\in\Pi(\mu,\nu)$ with $\int c\,d\pi^\star\le\int c\,d\pi$ for every $\pi\in\Pi(\mu,\nu)$;
--   2. the minimal cost equals the dual value:
--   $$\min_{\pi\in\Pi(\mu,\nu)}\int_{X\times Y}c(x,y)\,d\pi(x,y)=\sup\Big\{\int_X\psi\,d\mu+\int_Y\varphi\,d\nu\Big\},$$
--   where the supremum runs over all pairs $(\psi,\varphi)\in C_b(X)\times C_b(Y)$ of bounded continuous functions with $\psi(x)+\varphi(y)\le c(x,y)$ for all $x\in X$, $y\in Y$.
--
--   This is the central result of the source: the minimal total transportation cost equals the maximal revenue obtainable from competitive pickup and delivery prices.
--
--   **Formalization Note** Since $c\ge 0$ is not assumed integrable, the transport cost $\int c\,d\pi$ is the integral of a nonnegative function with values in $[0,\infty]$, and both sides of the equality are compared in the extended reals, so the case where every plan has infinite cost is included (the equality then says the dual supremum is $+\infty$). Polish spaces with Borel σ-algebras are the standing setting of Section 4.
-- source:
--   Colin Yao, *Monge–Kantorovich and Transportation Theory* (paper dated September 10, 2023), p. 6, Theorem 4.1 (statement of the Monge–Kantorovich theorem); cf. eq. (2.1), p. 4

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory

namespace MongeKantorovichYao

theorem monge_kantorovich_duality {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : X × Y → ℝ) (hc_cont : Continuous c) (hc_nonneg : ∀ p, 0 ≤ c p) :
    (∃ π ∈ transferencePlans μ ν, ∀ π' ∈ transferencePlans μ ν,
        ∫⁻ p, ENNReal.ofReal (c p) ∂π ≤ ∫⁻ p, ENNReal.ofReal (c p) ∂π') ∧
    (((⨅ π ∈ transferencePlans μ ν, ∫⁻ p, ENNReal.ofReal (c p) ∂π : ENNReal)) : EReal) =
      ⨆ (ψ : BoundedContinuousFunction X ℝ) (φ : BoundedContinuousFunction Y ℝ)
        (_ : ∀ x y, ψ x + φ y ≤ c (x, y)),
        (((∫ x, ψ x ∂μ) + (∫ y, φ y ∂ν) : ℝ) : EReal) := by sorry

end MongeKantorovichYao
