-- Prove2me | Theorems.Thm_FractionalSpectralGP_theorem_3_1
-- name    : FractionalSpectralGP.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:24:46.322097+00:00
-- url     : https://prove2.me/theorems/c63365fa-4820-4df0-ab38-75c0065beaca
-- title:
--   Theorem 3.1 — $(\sigma,\Lambda)$ is a spectral pair iff $\sum_{\lambda}|\widehat\sigma(t-\lambda)|^2=1$ (corrected: $\sigma$ a probability measure)
-- statement:
--   Let $\sigma$ be a Borel probability measure on $\mathbb R$ and let $\Lambda\subset\mathbb R$ be a discrete set. Then $(\sigma,\Lambda)$ is a spectral pair if and only if
--
--   $$
--   \sum_{\lambda\in\Lambda}\big|\widehat\sigma(t-\lambda)\big|^2=1\qquad\text{for every }t\in\mathbb R. \tag{3.1}
--   $$
--
--   The criterion (3.1) is what makes the coefficients of $W_\sigma(t)$ square-summable with sum $1$, so that $W_\sigma(t)$ lies in the white noise space itself.
--
--   **Formalization Note** The sum over $\Lambda$ is an unconditional sum of nonnegative terms.
--
--   Differences from the source:
--   - correction: σ a finite positive Borel measure → σ a Borel probability measure; reason: false as printed: σ = (1/√2)·Lebesgue on [0, 1], Λ = πℤ satisfies (3.1) for all t, but ‖e_λ‖² = σ(ℝ) = 1/√2, so (σ, Λ) is not a spectral pair
--   - reading: Λ a discrete set → every point of Λ is isolated (DiscreteTopology Λ), both in the hypothesis and in the definition of a spectral pair; reason: the weakest common meaning of discrete; the proof does not use discreteness
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Theorem 3.1, p.8

import Mathlib
import Definitions.Def_FractionalSpectralGP_sigmaHat
import Definitions.Def_FractionalSpectralGP_expL2
import Definitions.Def_FractionalSpectralGP_IsSpectralPair

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Theorem 3.1 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.8), corrected to probability measures: for a Borel
probability measure `σ` on `ℝ` and a discrete set `Λ ⊂ ℝ`, `(σ, Λ)` is a spectral pair if and only
if `Σ_{λ ∈ Λ} |σ̂(t − λ)|² = 1` for every `t ∈ ℝ` (3.1).

**Formalization Note.** The page says "finite positive Borel measure"; the statement is false for
`σ = (1/√2)·Leb|_{[0,1]}`, `Λ = πℤ` ((3.1) holds but `‖e_λ‖² = 1/√2`), so `σ` is a probability
measure here. The sum is an unconditional sum (`HasSum`) over `Λ`. -/
theorem theorem_3_1 (σ : Measure ℝ) [IsProbabilityMeasure σ] (Λ : Set ℝ)
    (hΛ : DiscreteTopology Λ) :
    IsSpectralPair σ Λ ↔ ∀ t : ℝ, HasSum (fun l : Λ => ‖sigmaHat σ (t - l)‖ ^ 2) 1 := by sorry

end FractionalSpectralGP
