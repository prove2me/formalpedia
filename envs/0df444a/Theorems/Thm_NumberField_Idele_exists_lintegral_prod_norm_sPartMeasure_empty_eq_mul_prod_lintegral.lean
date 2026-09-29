-- Prove2me | Theorems.Thm_NumberField_Idele_exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral
-- name    : NumberField.Idele.exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/61ecfa87-2f28-58a2-a5af-2764a0cf43cc
-- title:
--   Polar coordinates for the empty-part idelic Haar measure
-- statement:
--   Let $F$ be a number field. The assertion is the existence of a constant $C \in [0,\infty]$ with $C \neq 0$ and $C \neq \infty$, chosen independently of the data that follow, such that for every family $h \colon \mathrm{InfinitePlace}(F) \to (\mathbb{R} \to [0,\infty])$ of $[0,\infty]$-valued functions with $h_w$ measurable for each infinite place $w$, one has $$\int^{-} \prod_{w} h_w\bigl(\|a_\infty(w)\|\bigr)\, d\mu(a) \;=\; C \cdot \prod_{w} \int^{-}_{t \in (0,\infty)} h_w(t)\,\bigl(\mathrm{ofReal}\,t\bigr)^{-1}\,dt,$$ where the products are over all infinite places of $F$, the integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions, $a_\infty(w)$ denotes the $w$-component of the infinite-adelic (first) coordinate of the adele underlying the idele $a$, and $\mu =$ `sPartMeasure F ∅` is the measure on the idele group $(\mathbb{A}_F)^\times$ obtained as the push-forward, along the group homomorphism `partAt F ∅` induced by `Units.map` from the adelic ring map `partAtAdele F ∅`, of the restriction of the Haar measure `idelicHaar F` of $(\mathbb{A}_F)^\times$ to the subgroup of those ideles $\delta$ for which, at every finite place $v$ of $F$ (the exceptional set being empty), both $\delta_v$ and $(\delta^{-1})_v$ lie in the valuation ring of the completion at $v$; the right-hand factor $(\mathrm{ofReal}\,t)^{-1}$ is the multiplicative measure $dt/t$ on $(0,\infty)$.
--
--   This is the base case, with empty set of exceptional finite places, of the place-by-place evaluation of idelic integrals of product functions in the style of Tate's thesis: the archimedean part of the idelic Haar measure integrates radial product functions against $\prod_w dt/t$ up to one global constant, which absorbs the local polar-coordinate constants and the volume of the compact group of finite unit ideles. It is used in the convergence and analyticity estimates for torus integrals in the Rankin–Selberg and Whittaker computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral.lean

import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.Idele MeasureTheory
open scoped ENNReal

theorem NumberField.Idele.exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral
    (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧
      ∀ h : InfinitePlace F → ℝ → ℝ≥0∞, (∀ w, Measurable (h w)) →
        (∫⁻ a, ∏ w : InfinitePlace F, h w ‖((a : AdeleRing (𝓞 F) F).1 w)‖ ∂(sPartMeasure F ∅)) =
          C * ∏ w : InfinitePlace F, ∫⁻ t in Set.Ioi (0 : ℝ), h w t * (ENNReal.ofReal t)⁻¹ := by sorry
