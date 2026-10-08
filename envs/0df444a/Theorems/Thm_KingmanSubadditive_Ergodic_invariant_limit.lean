-- Prove2me | Theorems.Thm_KingmanSubadditive_Ergodic_invariant_limit
-- name    : KingmanSubadditive.Ergodic.invariant_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:42:17.37733+00:00
-- url     : https://prove2.me/theorems/1e3f4804-d60f-4e97-b2f6-092b5c474985
-- title:
--   (1.2.4): invariant σ-field representation of the limit
-- statement:
--   Let $x$ be a subadditive process, and let $\mathcal I$ be its path-defined shift-invariant σ-field. For any random variable $\xi$ that is the almost sure limit of $x_{0t}/t$, $\xi$ has an $\mathcal I$-measurable version and
--   $$\xi=\lim_{t\to\infty}t^{-1}E_P(x_{0t}\mid\mathcal I)\quad P\text{-almost surely}.$$
--   This describes how the random limit depends on the invariant information of the full process.
--
--   **Formalization Note** An almost sure limit is only determined up to a null set, so measurability is stated for an almost everywhere equal version. Conditional expectation is taken with respect to the explicit pullback of the path-space invariant σ-field.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 885, (1.2.3)–(1.2.4)

import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process

namespace KingmanSubadditive.Ergodic

open MeasureTheory Filter Topology

/-- Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973),
p. 885, (1.2.3)–(1.2.4). The limit is determined only up to a null set;
therefore its `𝓘`-measurability is expressed by an `𝓘`-measurable version.
`𝓘` is the pullback of the invariant σ-field on the full path space. -/
theorem invariant_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hx : IsSubadditiveProcess P x) (ξ : Ω → ℝ)
    (hξ : ∀ᵐ ω ∂P,
      Tendsto (fun t : ℕ => x 0 t ω / (t : ℝ)) atTop (𝓝 (ξ ω))) :
    (∃ η : Ω → ℝ, @Measurable Ω ℝ (invariantSigma x) _ η ∧
      η =ᵐ[P] ξ) ∧
    (∀ᵐ ω ∂P,
      Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * (P[x 0 t | invariantSigma x]) ω)
        atTop (𝓝 (ξ ω))) := by sorry

end KingmanSubadditive.Ergodic
