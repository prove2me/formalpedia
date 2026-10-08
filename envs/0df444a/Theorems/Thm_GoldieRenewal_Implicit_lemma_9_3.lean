-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_lemma_9_3
-- name    : GoldieRenewal.Implicit.lemma_9_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:08.417657+00:00
-- url     : https://prove2.me/theorems/9a4d6dc5-3bd4-4462-ba46-3d571be978e3
-- title:
--   Lemma 9.3 — if ∫₀^t u^κ P(R > u) du ~ C₊t, then P(R > t) ~ C₊t^{−κ}
-- statement:
--   Let $R$ be a real random variable, $\kappa>0$ and $C_+\in\mathbb R$. If
--   $$
--   \int_0^t u^\kappa P(R>u)\,du \sim C_+ t\qquad (t\to\infty),
--   $$
--   then
--   $$
--   P(R>t)\sim C_+t^{-\kappa}\qquad(t\to\infty).
--   $$
--
--   This Tauberian step turns the averaged statement delivered by the key renewal theorem into the pointwise tail asymptotics (2.10); monotonicity of $t\mapsto P(R>t)$ is what makes it possible.
--
--   **Formalization Note** "$\int_0^t\cdots\sim C_+t$" is read as $t^{-1}\int_0^t u^\kappa P(R>u)\,du\to C_+$ and "$P(R>t)\sim C_+t^{-\kappa}$" as $t^\kappa P(R>t)\to C_+$; for $C_+=0$ these are $o(t)$ and $o(t^{-\kappa})$, the paper's reading (p. 130).
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 143, Lemma 9.3

import Mathlib
open MeasureTheory Filter Topology

namespace GoldieRenewal.Implicit

/-- **Lemma 9.3** (Goldie 1991, Ann. Appl. Probab. 1(1), p. 143). If
`∫₀^t u^κ P(R > u) du ~ C₊ t` as `t → ∞`, then `P(R > t) ~ C₊ t^{−κ}` as `t → ∞`.

**Formalization Note** `R` is any real random variable and `κ > 0` (the standing exponent of §2).
"`~ C₊ t`" is read as `(∫₀^t u^κ P(R > u) du) / t → C₊` and "`P(R > t) ~ C₊ t^{−κ}`" as
`t^κ P(R > t) → C₊`, which includes the case `C₊ = 0` read as `o(t)` and `o(t^{−κ})` (the paper's
convention, p. 130). The integrand is bounded and measurable on `[0, t]`, so the interval integral is
the paper's value. -/
theorem lemma_9_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hR : Measurable R) (κ : ℝ) (hκ : 0 < κ) (C : ℝ)
    (h : Tendsto (fun t : ℝ => (∫ u in (0 : ℝ)..t, u ^ κ * P.real {ω | u < R ω}) / t)
      atTop (𝓝 C)) :
    Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop (𝓝 C) := by sorry

end GoldieRenewal.Implicit
