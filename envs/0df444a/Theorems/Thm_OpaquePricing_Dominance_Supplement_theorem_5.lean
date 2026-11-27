-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_theorem_5
-- name    : OpaquePricing.Dominance.Supplement.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T23:42:01.536052+00:00
-- url     : https://prove2.me/theorems/430fe7aa-95ca-4c18-898d-02f80f96fe14
-- title:
--   Theorem 5 — Arbitrary-law one-opaque bound and both i.i.d. sharpness endpoints
-- statement:
--   Let $N\ge2$, let $\mu$ be any probability law of nonnegative item valuations, and let $\alpha\in[0,1]$. No exchangeability or independence is required for the upper bound:
--   $$R_{1OPQ}(\mu,\alpha)\le\left(2-\frac{1-\alpha}{N}\right)R_{SP}(\mu).$$
--   Both endpoints are best possible even among i.i.d. laws. Precisely, for every $\varepsilon>0$ there is a nonnegative probability law $\nu_1$ with $0<R_{SP}(\nu_1^{\otimes N})<\infty$ such that
--   $$R_{1OPQ}(\nu_1^{\otimes N},1)>(2-\varepsilon)R_{SP}(\nu_1^{\otimes N}),$$
--   and there is a nonnegative probability law $\nu_0$ with $0<R_{SP}(\nu_0^{\otimes N})<\infty$ such that
--   $$R_{1OPQ}(\nu_0^{\otimes N},0)>\left(2-\frac1N-\varepsilon\right)R_{SP}(\nu_0^{\otimes N}).$$
--   The upper bound and both sharpness conclusions are a single theorem item. Each witness may depend on $N$ and $\varepsilon$; neither endpoint is restricted to two items.
--
--   Differences from the source:
--   - encoding: items 1 through N with N at least 2 → Fin N with the explicit premise 2 ≤ N; reason: zero-based indices preserve the full selling-model domain
--   - encoding: a pessimistic fraction α and a risk-neutral fraction 1−α → α ∈ [0,1] and the published independent mixture; reason: makes the probability range explicit and does not replace a mixture of revenues by a mixture of valuations
--   - encoding: nonnegative prices, expected revenues, and optimal prices → published highest-price choice revenue, nonnegative real prices, and ENNReal expectations and suprema; reason: preserves atomic and unbounded laws without an integrability or attained-optimum premise; the inherited supremum convention is disclosed in the published base mission
--   - reading: there exists an i.i.d. distribution such that the bounds are tight → for each positive ε, an i.i.d. law with ratio above the stated endpoint factor minus ε and finite positive SP revenue; reason: Example 5 takes z→0 and Example 6 takes a price supremum; tightness is the least universal factor, without asserting an attained ratio; the source all-N claim is retained at both endpoints
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Theorem 5, p. 23

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing
import Definitions.Def_OpaquePricing_Dominance_Supplement_OneOpaque

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

theorem theorem_5 {N : ℕ} (hN : 2 ≤ N) (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (α : ℝ) (hα : α ∈ Set.Icc 0 1) :
    optOne μ α ≤ ENNReal.ofReal (2 - (1 - α) / (N : ℝ)) * optSP μ ∧
    (∀ ε : ℝ, 0 < ε → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ᵐ x ∂ν, 0 ≤ x) ∧
      0 < optSP (Measure.pi (fun _ : Fin N => ν)) ∧
      optSP (Measure.pi (fun _ : Fin N => ν)) < ⊤ ∧
      ENNReal.ofReal (2 - ε) * optSP (Measure.pi (fun _ : Fin N => ν)) <
        optOne (Measure.pi (fun _ : Fin N => ν)) 1) ∧
    (∀ ε : ℝ, 0 < ε → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ᵐ x ∂ν, 0 ≤ x) ∧
      0 < optSP (Measure.pi (fun _ : Fin N => ν)) ∧
      optSP (Measure.pi (fun _ : Fin N => ν)) < ⊤ ∧
      ENNReal.ofReal (2 - 1 / (N : ℝ) - ε) * optSP (Measure.pi (fun _ : Fin N => ν)) <
        optOne (Measure.pi (fun _ : Fin N => ν)) 0) := by sorry

end OpaquePricing.Dominance.Supplement
