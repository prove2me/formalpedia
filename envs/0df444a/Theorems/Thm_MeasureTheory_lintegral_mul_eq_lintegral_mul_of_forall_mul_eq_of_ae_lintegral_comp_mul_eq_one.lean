-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one
-- name    : MeasureTheory.lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/227f07af-9a7e-560a-8376-7c9f25e70aa7
-- title:
--   Independence of the weight function in Weil's integration formula
-- statement:
--   Let $G$ be a group with a measurable structure for which multiplication $G \times G \to G$ is jointly measurable, and let $X$ be an additive group with a measurable structure for which negation is measurable. Let $\tau$ be an s-finite, right-translation-invariant measure on $G$ and $\mu$ an s-finite measure on $X$ invariant under $x \mapsto -x$. Let $n \colon X \to G$ be measurable and multiplicative in the sense that $n(x+y) = n(x)\,n(y)$ for all $x, y \in X$. Let $\Phi \colon G \to [0,\infty]$ be measurable and invariant under right translation by the image of $n$, i.e. $\Phi(g\,n(x)) = \Phi(g)$ for all $g \in G$ and $x \in X$. Let $w, w_0 \colon G \to [0,\infty]$ be measurable and suppose that for $\tau$-almost every $g \in G$ one has $\int_X w(g\,n(x))\,d\mu(x) = 1$, and likewise $\int_X w_0(g\,n(x))\,d\mu(x) = 1$ for $\tau$-almost every $g$. Then the lower Lebesgue integrals satisfy $\int_G w(g)\,\Phi(g)\,d\tau(g) = \int_G w_0(g)\,\Phi(g)\,d\tau(g)$.
--
--   This is the independence of the choice of weight (or section) function in Weil's integration formula $\int_G = \int_{G/N}\int_N$ for the subgroup $N = n(X)$, formulated so as to require neither a quotient measure on $G/N$ nor any closedness assumption on $N$: both sides compute the integral of $\Phi$ over $G/N$. It is used in the construction of Whittaker-type integrals for $\mathrm{GL}_2$, where the unipotent subgroup plays the role of $N$ and the weight is normalised to have unit integral along almost every coset.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.lintegral_mul_eq_lintegral_mul_of_forall_mul_eq_of_ae_lintegral_comp_mul_eq_one
    {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]
    (τ : Measure G) [SFinite τ] [τ.IsMulRightInvariant]
    (μ : Measure X) [SFinite μ] [μ.IsNegInvariant]
    (n : X → G) (hn : Measurable n) (hn_add : ∀ x y, n (x + y) = n x * n y)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦn : ∀ g x, Φ (g * n x) = Φ g)
    (w w₀ : G → ℝ≥0∞) (hw : Measurable w) (hw₀ : Measurable w₀)
    (h1 : ∀ᵐ g ∂τ, ∫⁻ x, w (g * n x) ∂μ = 1) (h1₀ : ∀ᵐ g ∂τ, ∫⁻ x, w₀ (g * n x) ∂μ = 1) :
    ∫⁻ g, w g * Φ g ∂τ = ∫⁻ g, w₀ g * Φ g ∂τ := by sorry
