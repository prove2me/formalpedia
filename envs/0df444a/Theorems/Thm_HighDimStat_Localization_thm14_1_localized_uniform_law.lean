-- Prove2me | Theorems.Thm_HighDimStat_Localization_thm14_1_localized_uniform_law
-- name    : HighDimStat.Localization.thm14_1_localized_uniform_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:31:53.644984+00:00
-- url     : https://prove2.me/theorems/d7c0c37b-69c2-476f-b1ff-88d1c189dd84
-- title:
--   A localized uniform law (Theorem 14.1)
-- statement:
--   **Theorem 14.1** (p. 455), the goal of this mission. Given a star-shaped and
--   $b$-uniformly bounded function class $F$, let $\delta_n$ be any positive solution of the
--   critical inequality $R_n(\delta;F)\le\delta^2/b$. Then for any $t\ge\delta_n$,
--   $$
--   \Big|\|f\|_n^2-\|f\|_2^2\Big|\le\frac12\|f\|_2^2+\frac{t^2}2\qquad\text{for all }f\in F,
--   $$
--   with probability at least $1-c_1e^{-c_2nt^2/b^2}$. If in addition
--   $n\delta_n^2\ge\frac2{c_2}\log(4\log(1/\delta_n))$, then
--   $$
--   \big|\|f\|_n-\|f\|_2\big|\le c_0\delta_n\qquad\text{for all }f\in F,
--   $$
--   with probability at least $1-c_1'e^{-c_2'n\delta_n^2/b^2}$.
--
--   This extends the earlier plain (unlocalized) uniform law of Chapter 4 (Theorem 4.10),
--   replacing an *absolute* deviation bound between $\|f\|_n^2$ and $\|f\|_2^2$ with a
--   *relative* one governed by the localized complexity — giving sharper control near the
--   origin, exactly the refinement Chapter 13's nonparametric-least-squares theory needs.
--
--   **Formalization Note** The two conclusions are kept as a conjunction with the second
--   gated behind its own extra hypothesis (`nδn² ≥ (2/c2)log(4log(1/δn))`), never merged into
--   a single implication, per the book's own two-part statement. The constants
--   `(c1,c2,c0,c1',c2')` are existentially quantified before every instance object (covariate
--   type, sample size, function class, `b`, `δn`, `t`), matching this book's standing
--   convention (stated once, in Chapter 2) that such constants are universal/absolute rather
--   than instance-dependent. **Revision 1**: every `f ∈ F` is required measurable
--   (`hF_meas : ∀ f ∈ F, Measurable f`) — not a separately numbered hypothesis in the book, but
--   a faithful addition making explicit what the book's own `L²(P)` framing (p. 454) already
--   assumes; without it, the population norm `‖f‖_2^2` appearing directly in the conclusion
--   could silently take the Bochner integral's junk value `0` for a non-measurable, pointwise-
--   bounded `f ∈ F`.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 455 (PDF p. 475), Theorem 14.1, Eqs. (14.5a), (14.5b)

import Mathlib
import Definitions.Def_HighDimStat_Localization_Core

namespace HighDimStat.Localization

open MeasureTheory

/-- **Theorem 14.1** (p. 455, PDF 475), the goal of this mission: a localized uniform law
relating the empirical and population `L²`-norms over a star-shaped, `b`-uniformly bounded
function class `F`. Let `δn` be any positive solution of the population critical inequality
(14.4). Then for any `t ≥ δn`, with probability at least `1 − c₁e^{-c₂nt²/b²}`,
`|‖f‖ₙ² − ‖f‖₂²| ≤ (1/2)‖f‖₂² + t²/2` holds simultaneously for every `f ∈ F` (Eq. 14.5a). If in
addition `nδn² ≥ (2/c₂)log(4log(1/δn))`, then with probability at least
`1 − c₁'e^{-c₂'nδn²/b²}`, `|‖f‖ₙ − ‖f‖₂| ≤ c₀δn` holds simultaneously for every `f ∈ F`
(Eq. 14.5b). The two conclusions have distinct hypotheses and are kept as a conjunction with
the second gated behind its own extra hypothesis, not merged into a single implication. Every
`f ∈ F` is required measurable (`hF_meas`): the book's own framing (p. 454, "𝔼[‖f‖ₙ²] = ‖f‖₂²
for any `f ∈ L²(P)`") implicitly restricts to measurable, square-integrable `f` throughout, and
without this hypothesis `popNormSq`'s Bochner integral could silently junk-collapse to `0` for a
non-measurable, pointwise-bounded `f ∈ F`, defeating the theorem's own localization mechanism. -/
theorem thm14_1_localized_uniform_law :
    ∃ c1 c2 c0 c1' c2' : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c0 ∧ 0 < c1' ∧ 0 < c2' ∧
      ∀ {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {n : ℕ}, 0 < n →
      ∀ (xs : Fin n → Ω → X) (eps : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
        (μ : Measure X) [IsProbabilityMeasure μ],
        IsIIDDesignWithRademacher xs eps P μ →
      ∀ (F : Set (X → ℝ)), IsStarShapedAroundOrigin F →
      ∀ (b : ℝ), 0 < b → IsUniformlyBounded F b → (∀ f ∈ F, Measurable f) →
      ∀ (δn t : ℝ), SatisfiesCriticalInequality xs eps P μ F b δn → δn ≤ t →
        (1 - c1 * Real.exp (-c2 * (n : ℝ) * t ^ 2 / b ^ 2) ≤
            P.real {ω | ∀ f ∈ F,
              |empiricalNormSq (fun i => xs i ω) f - popNormSq μ f| ≤
                (1 / 2) * popNormSq μ f + t ^ 2 / 2}) ∧
        ((n : ℝ) * δn ^ 2 ≥ (2 / c2) * Real.log (4 * Real.log (1 / δn)) →
          1 - c1' * Real.exp (-c2' * (n : ℝ) * δn ^ 2 / b ^ 2) ≤
            P.real {ω | ∀ f ∈ F,
              |empiricalNorm (fun i => xs i ω) f - popNorm μ f| ≤ c0 * δn}) := by sorry

end HighDimStat.Localization
