-- Prove2me | Theorems.Thm_MongeKantorovichYao_weak_duality
-- name    : MongeKantorovichYao.weak_duality
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T18:38:39.658886+00:00
-- url     : https://prove2.me/theorems/90a0c34d-1db8-466f-83f9-7c13e0258d42
-- title:
--   Section 3, eq. (3.1) — weak Monge–Kantorovich duality
-- statement:
--   Let $X,Y$ be measurable spaces, $\mu$ and $\nu$ measures on $X$ and $Y$, and $c : X\times Y\to\mathbb R$ a cost function. Let $\pi\in\Pi(\mu,\nu)$ be a transference plan with $c\in L^1(\pi)$, and let $\psi\in L^1(\mu)$, $\varphi\in L^1(\nu)$ satisfy $\psi(x)+\varphi(y)\le c(x,y)$ for all $x\in X$, $y\in Y$. Then
--   $$\int_X\psi\,d\mu+\int_Y\varphi\,d\nu\le\int_{X\times Y}c\,d\pi .$$
--
--   Taking the infimum over plans and the supremum over admissible pairs gives the weak duality inequality (3.1): $\inf_{\pi}\int c\,d\pi\ge\sup_{\psi,\varphi}\big(\int\psi\,d\mu+\int\varphi\,d\nu\big)$.
--
--   **Formalization Note** The statement is given plan-by-plan (equivalent to the inf/sup form). Integrability of $c$ with respect to $\pi$ is assumed so that $\int c\,d\pi$ is a genuine finite integral; the constraint $\psi+\varphi\le c$ is imposed at every point, as in the proof in the source.
-- source:
--   Colin Yao, *Monge–Kantorovich and Transportation Theory* (paper dated September 10, 2023), pp. 5–6, Section 3 (Weak Monge–Kantorovich), inequality (3.1) and its proof

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory

namespace MongeKantorovichYao

theorem weak_duality {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (c : X × Y → ℝ)
    (π : Measure (X × Y)) (hπ : π ∈ transferencePlans μ ν)
    (ψ : X → ℝ) (φ : Y → ℝ) (hψ : Integrable ψ μ) (hφ : Integrable φ ν)
    (hc : Integrable c π) (hfeas : ∀ x y, ψ x + φ y ≤ c (x, y)) :
    ∫ x, ψ x ∂μ + ∫ y, φ y ∂ν ≤ ∫ p, c p ∂π := by sorry

end MongeKantorovichYao
