-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_hazard_odds_envelope
-- name    : IndependentInfoPricing.Main.Supplement.hazard_odds_envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:50:40.752728+00:00
-- url     : https://prove2.me/theorems/5a8d13c3-c66c-4d3a-aaf0-fb798dd79bbf
-- title:
--   Corollary 4.5 — Hazard-odds envelope bound
-- statement:
--   Let $X\ge0$ be a regular magnitude in the scope of §4.2 with smallest monopoly price $p^0_X$ and dimensionless hazard $\eta_X$. For $0<s\le t\le p^0_X$ with $\eta_X(s)>0$,
--   $$1-\eta_X(t)\le\frac st\cdot\frac{1-\eta_X(s)}{\eta_X(s)}.$$
--
--   The bound is applied to both magnitudes $X$ and $Y$ (the source also writes it for $Y$); a single statement for an arbitrary regular magnitude covers both. It is the quantitative estimate used inside the single-bound lemma (Lemma 4.6).
--
--   **Formalization Note** $\eta_X$ takes values in $[0,\infty]$; it can be $+\infty$ only at the left endpoint of the support, where the right-hand side of the source's inequality is undefined, so $\eta_X(s)<\infty$ is assumed. When $\eta_X(s)$ is finite so is $\eta_X(t)$, and both are compared as real numbers.
--
--   Differences from the source:
--   - reading: a continuously differentiable density, positive throughout an interval support, with pointwise values at a finite left endpoint understood as right limits (possibly extended) → a density version f : ℝ → [0,∞] that is finite, positive and C¹ on the interior of the topological support, the support being an interval; the hazard η at the left endpoint is the liminf of t·f(t)/S(t) from the interior; reason: endpoint values are one-sided limits in the source, so positivity is imposed where the density is evaluated pointwise (the interior); the liminf equals the source's one-sided limit whenever that limit exists, which regularity guarantees
--   - encoding: regularity: ψ_D(t) = t − 1/h_D(t) nondecreasing on the support → ψ_D(t) = t − S_D(t)/f(t) monotone on the interior of the support; reason: the endpoint values of ψ_D are one-sided limits of interior values, so monotonicity on the interior is monotonicity on the support
--   - encoding: η_X(s) > 0, with the source's right-hand side (1 − η_X(s))/η_X(s) → 0 < η_X(s) and η_X(s) ≠ ∞ in [0,∞], real arithmetic on toReal; reason: η_X(s) = ∞ can occur only at the left endpoint, where the source's expression is undefined; the condition excludes only that undefined case
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Corollary 4.5, printed p.28 (PDF p.30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_Regularity

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Corollary 4.5, p.28 (PDF 30): for a regular magnitude and `0 < s ≤ t ≤ p⁰_D` with
`η_D(s) > 0` (finite), `1 − η_D(t) ≤ (s/t)(1 − η_D(s))/η_D(s)`. -/
theorem hazard_odds_envelope (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (hD : MagnitudeScope D f)
    (hreg : Regular D f) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ monopolyPrice D)
    (hη : 0 < eta D f s) (hηfin : eta D f s ≠ ⊤) :
    1 - etaReal D f t ≤ s / t * ((1 - etaReal D f s) / etaReal D f s) := by sorry


end IndependentInfoPricing.Main.Supplement
