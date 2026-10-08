-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_lemma_4_1
-- name    : MeanFieldPDE.Classical.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:39.298816+00:00
-- url     : https://prove2.me/theorems/39ab33bb-7778-488d-abd8-9c662f8b088a
-- title:
--   Lemma 4.1, p. 20 — ∂_{x_l}(∂_μ g(x,μ,y)) = ∂_μ(∂_{x_l} g(x,μ))(y) for g ∈ C^{2,1}_b(ℝ^d × P₂(ℝ^d))
-- statement:
--   Let $g:\mathbb R^d\times\mathcal P_2(\mathbb R^d)\to\mathbb R$ belong to $C^{2,1}_b(\mathbb R^d\times\mathcal P_2(\mathbb R^d))$ in the sense of Hypothesis (H.2). Then for all $1\le l\le d$,
--   $$\partial_{x_l}\big(\partial_\mu g(x,\mu,y)\big)=\partial_\mu\big(\partial_{x_l}g(x,\mu)\big)(y),\qquad(x,\mu,y)\in\mathbb R^d\times\mathcal P_2(\mathbb R^d)\times\mathbb R^d.$$
--
--   This is the Schwarz symmetry for mixed derivatives in the space variable and the measure; it is used for the coefficients and for the value function (Lemma 5.2).
--
--   **Formalization Note** Stated for one real-valued component (the paper's $g$ is the pair $(\sigma,b)$, componentwise), as an identity of the vector components $j$, for the derivative witnesses of the class.
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, p. 20, Lemma 4.1

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- Lemma 4.1, p. 20 (symmetry of the mixed derivatives): if `g ∈ C^{2,1}_b(ℝ^d × P₂(ℝ^d))` in
the sense of (H.2), with derivatives `D`, then for all `1 ≤ l ≤ d`,
`∂_{x_l}(∂_μ g(x, μ, y)) = ∂_μ(∂_{x_l} g(x, μ))(y)` for all `(x, μ, y) ∈ ℝ^d × P₂(ℝ^d) × ℝ^d`
(componentwise in `j`). Stated for one scalar component of `(σ, b)`. -/
theorem lemma_4_1 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (g : E d → Measure (E d) → ℝ) (D : Deriv2 d) (hg : IsC21bWith P g D) :
    ∀ (x : E d) (μ : Measure (E d)) (y : E d), IsP2 μ → ∀ l j : Fin d,
      D.DxDμ x μ y j l = D.DμDx x μ l y j := by sorry

end MeanFieldPDE.Classical
