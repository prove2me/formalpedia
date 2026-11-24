-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_theorem_3
-- name    : OpaquePricing.Dominance.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:38:32.023293+00:00
-- url     : https://prove2.me/theorems/4dc3de66-0720-464d-8278-b8f91b9c4c68
-- title:
--   Theorem 3 — Exchangeable revenue bounds and a separating law
-- statement:
--   Let $N\ge2$, let $\mu$ be an exchangeable probability law of nonnegative valuations, and let $\alpha\in[0,1]$. All three conclusions hold:
--   $$R_{DP}(\mu)\le(1+\log N)R_{SP}(\mu),\qquad R_{OPQ}(\mu,\alpha)\le NR_{SP}(\mu).$$
--   There also exists an exchangeable nonnegative probability law $F_N$, specifically the uniform-permutation law in Example 4, with $0<R_{DP}(F_N)<\infty$ and $0<R_{SP}(F_N)\le2$, and with $R_{OPQ}(F_N,\alpha)\ge\alpha N$, such that
--   $$R_{OPQ}(F_N,\alpha)\ge\frac\alpha2\frac{N}{1+\log N}R_{DP}(F_N).$$
--   Here $\log$ denotes the natural logarithm. The first two inequalities apply to every such law; the separating law can be chosen afresh for every $N$ and $\alpha$. This includes every clause of the source theorem.
--
--   Differences from the source:
--   - encoding: items 1 through N with N at least 2 → Fin N with the explicit premise 2 ≤ N; reason: zero-based indices preserve the full selling-model domain
--   - encoding: a pessimistic fraction α and a risk-neutral fraction 1−α → α ∈ [0,1] and the published independent mixture; reason: makes the probability range explicit and does not replace a mixture of revenues by a mixture of valuations
--   - encoding: nonnegative prices, expected revenues, and optimal prices → published highest-price choice revenue, nonnegative real prices, and ENNReal expectations and suprema; reason: preserves atomic and unbounded laws without an integrability or attained-optimum premise; the inherited supremum convention is disclosed in the published base mission
--   - generalization: the bare existential separation in Theorem 3(iii) → an existential law equal to exampleLaw N, with probability, exchangeability, nonnegativity and positive finite DP revenue and the explicit Example 4 bounds SP≤2 and OPQ≥αN asserted as conclusions; reason: strengthens the existential by the source-supported Example 4 construction and its explicit revenue bounds; it implies the complete source conclusion and prevents a zero-law or infinite-revenue witness
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Theorem 3, p. 21

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing
import Definitions.Def_OpaquePricing_Dominance_Supplement_ExampleLaw

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

theorem theorem_3 {N : ℕ} (hN : 2 ≤ N) (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (α : ℝ) (hα : α ∈ Set.Icc 0 1) (hex : Exchangeable μ) :
    optDP μ ≤ ENNReal.ofReal (1 + Real.log N) * optSP μ ∧
    optOPQ μ α ≤ (N : ENNReal) * optSP μ ∧
    ∃ ρ : Measure (Fin N → ℝ), ρ = exampleLaw N ∧ IsProbabilityMeasure ρ ∧
      Exchangeable ρ ∧ (∀ᵐ v ∂ρ, ∀ i, 0 ≤ v i) ∧
      0 < optDP ρ ∧ optDP ρ < ⊤ ∧
      0 < optSP ρ ∧ optSP ρ ≤ 2 ∧
      ENNReal.ofReal (α * N) ≤ optOPQ ρ α ∧
      ENNReal.ofReal (α / 2 * ((N : ℝ) / (1 + Real.log N))) * optDP ρ ≤
        optOPQ ρ α := by sorry

end OpaquePricing.Dominance.Supplement
