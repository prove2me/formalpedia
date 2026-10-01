-- Prove2me | Theorems.Thm_MongeKantorovichYao_integral_fst_eq_of_mem_transferencePlans
-- name    : MongeKantorovichYao.integral_fst_eq_of_mem_transferencePlans
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T21:11:16.477736+00:00
-- url     : https://prove2.me/theorems/5fc0ce75-1681-4e5e-94ec-060cb741911b
-- title:
--   Theorem 4.32 — integrating against a marginal
-- statement:
--   Let $X,Y$ be measurable spaces and let $\pi$ be a probability measure on $X\times Y$ with marginals $\mu$ and $\nu$ on $X$ and $Y$ respectively. Then for every $\mu$-integrable $f : X\to\mathbb R$,
--   $$\int_X f(x)\,d\mu(x)=\int_{X\times Y}f(x)\,d\pi(x,y).$$
--
--   This identity converts the dual objective $\int\psi\,d\mu+\int\varphi\,d\nu$ into a single integral against a plan.
--
--   **Formalization Note** The function $(x,y)\mapsto f(x)$ is the extension $\tilde f$ mentioned in the source; the analogous statement for the second marginal is symmetric.
-- source:
--   Colin Yao, *Monge–Kantorovich and Transportation Theory* (paper dated September 10, 2023), p. 16, Theorem 4.32

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory

namespace MongeKantorovichYao

theorem integral_fst_eq_of_mem_transferencePlans {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (π : Measure (X × Y)) (hπ : π ∈ transferencePlans μ ν)
    (f : X → ℝ) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ p, f p.1 ∂π := by sorry

end MongeKantorovichYao
