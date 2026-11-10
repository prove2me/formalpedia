-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_fact_3_1
-- name    : GoodHypotheses.Proper.fact_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:14:50.56649+00:00
-- url     : https://prove2.me/theorems/b35b148d-80ef-4631-996a-12125f1dbe9d
-- title:
--   Fact 3.1 — the Scheffé identity for the generalized TV distance
-- statement:
--   Let $f,g$ be nonnegative integrable densities on $(X,\mu)$ and $S$ a Scheffé function of $(f,g)$. Then
--   $$d_{TV}(f,g)=\int fS\,d\mu-\int gS\,d\mu+\frac{\|g\|_1-\|f\|_1}2 .$$
--   This identity is the basis of every estimator in the paper: it expresses a TV distance through integrals of a single $[0,1]$-valued test function.
--
--   Differences from the source:
--
--   - encoding: nonnegative, integrable densities → functions X → ℝ, nonnegative at every point and μ-integrable (Bochner); reason: the paper's nonnegative integrable densities (Definition 2); integrability keeps every integral genuine
--   - encoding: S a Scheffé function (Definition 3) → IsScheffe and S measurable; reason: the integrals ∫ fS dµ of the statement presuppose that S is measurable
--   - encoding: ‖f‖₁ → ∫ f dμ; reason: equal for a nonnegative integrable f
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 13, Fact 3.1

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_Densities

open MeasureTheory

namespace GoodHypotheses.Proper

/-- Fact 3.1 (p. 13): for nonnegative integrable densities `f, g` and a (measurable) Scheffé
function `S` of `(f, g)`, `dTV(f, g) = ∫ fS dμ − ∫ gS dμ + (‖g‖₁ − ‖f‖₁)/2`, where
`‖f‖₁ = ∫ f dμ` because `f ≥ 0`. -/
theorem fact_3_1 {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g S : X → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hf : Integrable f μ) (hg : Integrable g μ)
    (hS : IsScheffe f g S) (hSm : Measurable S) :
    tvDist μ f g = ∫ x, f x * S x ∂μ - ∫ x, g x * S x ∂μ
      + ((∫ x, g x ∂μ) - ∫ x, f x ∂μ) / 2 := by sorry

end GoodHypotheses.Proper
