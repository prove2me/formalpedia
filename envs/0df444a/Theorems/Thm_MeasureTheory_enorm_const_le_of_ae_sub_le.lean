-- Prove2me | Theorems.Thm_MeasureTheory_enorm_const_le_of_ae_sub_le
-- name    : MeasureTheory.enorm_const_le_of_ae_sub_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T21:36:11.979682+00:00
-- url     : https://prove2.me/theorems/60319b5b-9515-4ff6-ab63-2ba1f4e88927
-- title:
--   A constant controlled by an Lp norm and a uniform oscillation bound
-- statement:
--   Let $(X,\mu)$ be a measure space with $0<\mu(X)<\infty$, let $1\le p<\infty$, and let $f:X\to\mathbb R$ be almost everywhere strongly measurable. If $c\in\mathbb R$ and $K\in[0,\infty]$ satisfy $|c-f(y)|\le K$ almost everywhere, then
--   $$|c|\le K+\mu(X)^{-1/p}\|f\|_{L^p(\mu)}.$$
--   This finite-measure estimate turns a local oscillation bound into a pointwise size bound. It applies to arbitrary finite measures, including restrictions to balls.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, p. 70, proof of Theorem 3.36, final unit-ball averaging argument; generalized to finite measure spaces

import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

open MeasureTheory

theorem MeasureTheory.enorm_const_le_of_ae_sub_le {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ENNReal}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) (hμ0 : μ Set.univ ≠ 0) (hμt : μ Set.univ ≠ ⊤)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (c : ℝ) (K : ENNReal)
    (hK : ∀ᵐ y ∂μ, ‖c - f y‖ₑ ≤ K) :
    ‖c‖ₑ ≤ K + (μ Set.univ ^ (1 / p.toReal))⁻¹ * eLpNorm f p μ := by sorry
