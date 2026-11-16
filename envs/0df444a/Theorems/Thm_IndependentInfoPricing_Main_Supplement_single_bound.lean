-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_single_bound
-- name    : IndependentInfoPricing.Main.Supplement.single_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:51:43.47157+00:00
-- url     : https://prove2.me/theorems/e67de72e-2763-4934-9772-cab306377f60
-- title:
--   Lemma 4.6 — Single-bound lemma
-- statement:
--   Let $X,Y\ge0$ be independent regular magnitudes in the scope of §4.2, $Z=\min\{X,Y\}$, and $\operatorname{Rel}_X=\mathbb E[H_X(Y)]$, $\operatorname{Rel}_Y=\mathbb E[H_Y(X)]$ as in Lemma 4.3. Then:
--
--   1. for every $p_X\le p^0_X$ with $0<\eta_X(p_X)<1$,
--   $$\operatorname{Rel}_X\le\rho_X(p_X)+\operatorname{Rev}(Z)\cdot\frac{1-\eta_X(p_X)}{\eta_X(p_X)};\tag{i}$$
--   2. for every $p_Y\le p^0_Y$ with $0<\eta_Y(p_Y)<1$,
--   $$\operatorname{Rel}_Y\le\rho_Y(p_Y)+\operatorname{Rev}(Z)\cdot\frac{1-\eta_Y(p_Y)}{\eta_Y(p_Y)}.\tag{ii}$$
--
--   Here $\rho_D(t)=t\,S_D(t)$ and $\operatorname{Rev}(Z)=\sup_{p\ge0}p\Pr(Z\ge p)$. The lemma compares each single-direction relaxation with the full-revelation revenue $\operatorname{Rev}(Z)$ and is the key inequality of the proof of Theorem 4.1.
--
--   **Formalization Note** $\operatorname{Rev}(Z)$ is the published `scalarRevenue` of the law of $\min\{X,Y\}$ under $X\otimes Y$.
--
--   Differences from the source:
--   - reading: a continuously differentiable density, positive throughout an interval support, with pointwise values at a finite left endpoint understood as right limits (possibly extended) → a density version f : ℝ → [0,∞] that is finite, positive and C¹ on the interior of the topological support, the support being an interval; the hazard η at the left endpoint is the liminf of t·f(t)/S(t) from the interior; reason: endpoint values are one-sided limits in the source, so positivity is imposed where the density is evaluated pointwise (the interior); the liminf equals the source's one-sided limit whenever that limit exists, which regularity guarantees
--   - encoding: regularity: ψ_D(t) = t − 1/h_D(t) nondecreasing on the support → ψ_D(t) = t − S_D(t)/f(t) monotone on the interior of the support; reason: the endpoint values of ψ_D are one-sided limits of interior values, so monotonicity on the interior is monotonicity on the support
--   - reading: for any p_X … and any p_Y …: (i); (ii) → (i) for every admissible p_X, and separately (ii) for every admissible p_Y; reason: (i) involves only p_X and (ii) only p_Y; stating them separately does not require an admissible p_Y to exist in order to use (i)
--   - encoding: real expected revenues, suprema and probabilities → nonnegative extended reals (ℝ≥0∞): lintegrals, suprema and measures; reason: the base mission's convention; it represents every finite value unchanged and avoids default-zero integrals
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.6, printed p.29 (PDF p.31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_TwoItem

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Lemma 4.6, p.29 (PDF 31): the single-bound lemma, (i) for `Rel_X` and (ii) for `Rel_Y`. -/
theorem single_bound (X Y : Measure ℝ) (fX fY : ℝ → ℝ≥0∞)
    (hX : MagnitudeScope X fX) (hY : MagnitudeScope Y fY)
    (hXr : Regular X fX) (hYr : Regular Y fY) :
    (∀ pX : ℝ, pX ≤ monopolyPrice X → 0 < eta X fX pX → eta X fX pX < 1 →
      relValue X Y ≤ ENNReal.ofReal (revenueCurve X pX) +
        scalarRevenue (minLaw X Y) * ENNReal.ofReal ((1 - etaReal X fX pX) / etaReal X fX pX)) ∧
    (∀ pY : ℝ, pY ≤ monopolyPrice Y → 0 < eta Y fY pY → eta Y fY pY < 1 →
      relValue Y X ≤ ENNReal.ofReal (revenueCurve Y pY) +
        scalarRevenue (minLaw X Y) * ENNReal.ofReal ((1 - etaReal Y fY pY) / etaReal Y fY pY)) := by sorry


end IndependentInfoPricing.Main.Supplement
