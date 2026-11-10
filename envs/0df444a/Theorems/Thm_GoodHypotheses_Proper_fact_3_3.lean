-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_fact_3_3
-- name    : GoodHypotheses.Proper.fact_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:15:00.509502+00:00
-- url     : https://prove2.me/theorems/71ca5a46-27c7-4896-bf4f-310f1ee06559
-- title:
--   Fact 3.3 — a Scheffé function of (f, g) lower-bounds d_TV(f, p)
-- statement:
--   Let $f,g$ be nonnegative integrable densities with Scheffé function $S$, and $p$ another nonnegative integrable density. Then
--   $$d_{TV}(f,p)\ \ge\ \int fS\,d\mu-\int pS\,d\mu+\frac{\|p\|_1-\|f\|_1}2 .$$
--   It certifies a lower bound on the distance to the unknown $p$, to which there is no density access.
--
--   Differences from the source:
--
--   - encoding: nonnegative, integrable densities → functions X → ℝ, nonnegative at every point and μ-integrable (Bochner); reason: the paper's nonnegative integrable densities (Definition 2); integrability keeps every integral genuine
--   - encoding: S a Scheffé function (Definition 3) → IsScheffe and S measurable; reason: the integrals ∫ fS dµ of the statement presuppose that S is measurable
--   - encoding: ‖f‖₁ → ∫ f dμ; reason: equal for a nonnegative integrable f
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 14, Fact 3.3

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_Densities

open MeasureTheory

namespace GoodHypotheses.Proper

/-- Fact 3.3 (p. 14): for nonnegative integrable densities `f, g` with a (measurable) Scheffé
function `S` of `(f, g)`, and another nonnegative integrable density `p`,
`dTV(f, p) ≥ ∫ fS dμ − ∫ pS dμ + (‖p‖₁ − ‖f‖₁)/2`. -/
theorem fact_3_3 {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g p S : X → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hp0 : ∀ x, 0 ≤ p x)
    (hf : Integrable f μ) (hg : Integrable g μ) (hp : Integrable p μ)
    (hS : IsScheffe f g S) (hSm : Measurable S) :
    ∫ x, f x * S x ∂μ - ∫ x, p x * S x ∂μ + ((∫ x, p x ∂μ) - ∫ x, f x ∂μ) / 2
      ≤ tvDist μ f p := by sorry

end GoodHypotheses.Proper
