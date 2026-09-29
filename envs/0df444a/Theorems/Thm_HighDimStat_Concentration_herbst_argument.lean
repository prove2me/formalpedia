-- Prove2me | Theorems.Thm_HighDimStat_Concentration_herbst_argument
-- name    : HighDimStat.Concentration.herbst_argument
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:15:08.189977+00:00
-- url     : https://prove2.me/theorems/d0eaa3cc-965c-4e72-bf6b-76b527d178b2
-- title:
--   Proposition 3.2 -- the Herbst argument
-- statement:
--   **Proposition 3.2 (Herbst argument).** Suppose that the entropy $H(e^{\lambda X})$
--   satisfies
--
--   $$
--   H(e^{\lambda X}) \;\le\; \tfrac12\sigma^2\lambda^2\,\varphi_X(\lambda)
--   $$
--
--   for all $\lambda\in I$, where $I$ can be either $[0,\infty)$ or $\mathbb R$, and
--   $\varphi_X(\lambda):=\mathbb E[e^{\lambda X}]$. Then $X$ satisfies
--
--   $$
--   \log\mathbb E[e^{\lambda(X-\mathbb E[X])}] \;\le\; \tfrac12\lambda^2\sigma^2 \qquad \text{for all } \lambda\in I.
--   $$
--
--   This is the foundational bridge of the chapter's entropic method: an upper bound on the
--   $\varphi$-entropy of the exponential moment translates directly into a sub-Gaussian bound on
--   the cumulant generating function itself, and hence (via the usual Chernoff argument) into a
--   sub-Gaussian tail bound.
--
--   **Formalization Note** $I=[0,\infty)$ or $I=\mathbb R$ is realized as a disjunctive
--   hypothesis on a `Set ℝ` parameter, both the entropy hypothesis and the conclusion quantified
--   over `∀ λ ∈ I`, exactly capturing the book's "for all `λ∈I`" in both directions
--   simultaneously rather than duplicating the theorem for the two cases. Explicit `Integrable`
--   hypotheses guard the Bochner integral's junk value on a non-integrable function (trap 2).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 60 (PDF p. 80), Proposition 3.2, Eqs. (3.5)-(3.6)

import Mathlib
import Definitions.Def_HighDimStat_Concentration_phiEntropy

open MeasureTheory

namespace HighDimStat.Concentration

/-- **Proposition 3.2** (Herbst argument), Wainwright, *High-Dimensional Statistics* (2019),
p. 60. Suppose that the entropy `H(e^{λX})` satisfies `H(e^{λX}) ≤ (1/2)σ²λ²φ_X(λ)` for all
`λ ∈ I`, where `I` is either `[0,∞)` or `ℝ`. Then `X` satisfies
`log E[e^{λ(X-E[X])}] ≤ (1/2)λ²σ²` for all `λ ∈ I`. -/
theorem herbst_argument {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (X : Ω → ℝ) (sigma : ℝ) (I : Set ℝ)
    (hI : I = Set.Ici 0 ∨ I = Set.univ)
    (hInt : ∀ lam ∈ I, Integrable (fun ω => Real.exp (lam * X ω)) Prob ∧
      Integrable (fun ω => Real.exp (lam * X ω) * Real.log (Real.exp (lam * X ω))) Prob)
    (hEntropy : ∀ lam ∈ I,
      phiEntropy (fun ω => Real.exp (lam * X ω)) Prob ≤
        1 / 2 * sigma ^ 2 * lam ^ 2 * ∫ ω, Real.exp (lam * X ω) ∂Prob) :
    ∀ lam ∈ I,
      Real.log (∫ ω, Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob)) ∂Prob) ≤
        1 / 2 * lam ^ 2 * sigma ^ 2 := by sorry

end HighDimStat.Concentration
