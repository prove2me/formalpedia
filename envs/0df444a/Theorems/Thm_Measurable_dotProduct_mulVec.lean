-- Prove2me | Theorems.Thm_Measurable_dotProduct_mulVec
-- name    : Measurable.dotProduct_mulVec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:37.281427+00:00
-- url     : https://prove2.me/theorems/ca284aa5-fd64-4cf9-b753-ab2c5fcb59d1
-- title:
--   Measurability of a quadratic form in a measurable matrix field
-- statement:
--   Let $(\Omega, \mathcal F)$ be a measurable space, let
--   $M : \Omega \to \mathbb{R}^{d \times d}$ be a matrix-valued map whose every entry
--   $\omega \mapsto M(\omega)_{ij}$ is measurable, and let $v, w : \Omega \to \mathbb{R}^d$ be
--   measurable. Then the quadratic expression
--
--   $$
--   \omega \;\longmapsto\; v(\omega)^{\mathsf T}\, M(\omega)\, w(\omega) \;=\; \sum_{i,j} v(\omega)_i\, M(\omega)_{ij}\, w(\omega)_j
--   $$
--
--   is measurable.
--
--   Entrywise measurability of a random matrix is what one verifies in practice, while the
--   quantities that appear in a proof are quadratic forms in it. This lemma is the step between the
--   two, needed whenever a self-normalized statistic or a random quadratic form is to be integrated
--   or bounded in probability.
--
--   **Formalization Note** The expression is `v ω ⬝ᵥ M ω *ᵥ w ω`, using
--   `Matrix.dotProduct` and `Matrix.mulVec`; the index type is `Fin d`.
-- source:
--   Elementary measurability of a finite bilinear expression; carved from the accepted proof of ImprovedLinBandits.OFUL.oful_regret_bound, https://prove2.me/submissions/028e111f-382d-40d0-8008-127228d5e6cf

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Matrix NNReal

theorem Measurable.dotProduct_mulVec {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {M : Ω → Matrix (Fin d) (Fin d) ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j)
    {v w : Ω → Fin d → ℝ} (hv : Measurable v) (hw : Measurable w) :
    Measurable fun ω => v ω ⬝ᵥ M ω *ᵥ w ω := by sorry
