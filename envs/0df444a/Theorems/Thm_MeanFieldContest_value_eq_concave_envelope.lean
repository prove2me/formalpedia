-- Prove2me | Theorems.Thm_MeanFieldContest_value_eq_concave_envelope
-- name    : MeanFieldContest.value_eq_concave_envelope
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:59.930474+00:00
-- url     : https://prove2.me/theorems/98958b9d-09db-4602-873b-43ac7824a831
-- title:
--   §3.2 display — $u^F(x_0)=(\xi^F\circ h^{-1})^{conc}(1)\le\Phi(F)^{conc}(1)$, with equality at an equilibrium
-- statement:
--   Let $R$ be a reward function, $\mu<\bar\mu_\infty$ and $F\in\mathcal F$. With $h(x_0)=1$ and $\mathrm{conc}$ the concave envelope,
--   $$u^F(x_0)=(\xi^F\circ h^{-1})^{conc}(1)\le(g\circ F\circ h^{-1})^{conc}(1),$$
--   and the inequality is an equality if $F$ is a mean field equilibrium.
--
--   This identity converts the player's stopping problem into a problem about the concave envelope of one function, on which the uniqueness proof operates.
--
--   Differences from the source:
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: concave envelope on ℝ₊, with F∘h⁻¹ and ξ^F∘h⁻¹ on [0, h(∞)] → concOn on D = [0, h(∞)] ∩ ℝ (supremum over finite convex combinations), with F∘h⁻¹(h(∞)) := 1 and ξ^F∘h⁻¹(h(∞)) := g(1) when h(∞) < ∞; reason: D is ℝ₊ for µ ≤ 0 and the functions are not defined beyond h(∞) for µ > 0; the values at h(∞) are the limits; for these bounded functions the supremum is the smallest concave majorant at points of D
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, §3.2, display after “Dynamic programming and optimal stopping theory yield”, p.12

import Mathlib
import Definitions.Def_TractableComposite_concOn
import Definitions.Def_MeanFieldContest_Model
import Definitions.Def_MeanFieldContest_EnvelopeObjects

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **§3.2, display after "Dynamic programming and optimal stopping theory yield"**, arXiv:2103.04219v1, p.12.
Under §3.2's standing assumptions, for `F ∈ 𝓕`,
`u^F(x₀) = (ξ^F ∘ h⁻¹)^conc(1) ≤ (g ∘ F ∘ h⁻¹)^conc(1)`, and the inequality is an equality if `F` is a
mean field equilibrium.

**Formalization Note.** The paper's "concave envelope on `ℝ₊`" is `concOn` on `D = [0, h(∞)] ∩ ℝ`, the
domain of `ξ^F ∘ h⁻¹`; this is `ℝ₊` for `µ ≤ 0`, and for `µ > 0` the function is not defined beyond
`h(∞)`. The set of `concOn` is nonempty at `1 ∈ D` and bounded above by `g(1)`. -/
theorem value_eq_concave_envelope {x₀ μ σ : ℝ} {R : ℝ → ℝ} {F : Measure ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : IsRewardFunction R) (hμ : μ < muBarInfty R x₀ σ)
    (hF : F ∈ feasibleLaws x₀ μ σ) :
    valueFn μ σ R F x₀ = TractableComposite.concOn (hDomain x₀ μ σ) (xiScale x₀ μ σ R F) 1 ∧
      TractableComposite.concOn (hDomain x₀ μ σ) (xiScale x₀ μ σ R F) 1 ≤
        TractableComposite.concOn (hDomain x₀ μ σ) (Phi x₀ μ σ R F) 1 ∧
      (IsMFE x₀ μ σ R F →
        TractableComposite.concOn (hDomain x₀ μ σ) (xiScale x₀ μ σ R F) 1 =
          TractableComposite.concOn (hDomain x₀ μ σ) (Phi x₀ μ σ R F) 1) := by sorry

end MeanFieldContest
