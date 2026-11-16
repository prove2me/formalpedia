-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_truncated_regular_revenue
-- name    : IndependentInfoPricing.Main.Supplement.truncated_regular_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:54:14.484671+00:00
-- url     : https://prove2.me/theorems/de27377a-2a82-4a46-a526-e7bf59dfc876
-- title:
--   Lemma 4.13 — Truncated regular revenue
-- statement:
--   Let $D\ge0$ be a regular magnitude in the scope of §4.4 (positive continuously differentiable density on an interval support, finite monopoly price), with survival function $S(p)=\Pr(D\ge p)$ and $r=\operatorname{Rev}(D)=\sup_{p\ge0}p\,S(p)$. Then for every $t\ge0$,
--   $$\sup_{0\le p\le t}p\,S(p)\ge\frac12\min\{r,t\}.\tag{62}$$
--
--   A price cap at level $t$ thus costs a regular seller at most a factor two relative to $\min\{r,t\}$. The lemma yields the half-tail property (Corollary 4.14) and budget-constrained extraction (Lemma 4.15).
--
--   Differences from the source:
--   - reading: a continuously differentiable density, positive throughout an interval support, with pointwise values at a finite left endpoint understood as right limits (possibly extended) → a density version f : ℝ → [0,∞] that is finite, positive and C¹ on the interior of the topological support, the support being an interval; the hazard η at the left endpoint is the liminf of t·f(t)/S(t) from the interior; reason: endpoint values are one-sided limits in the source, so positivity is imposed where the density is evaluated pointwise (the interior); the liminf equals the source's one-sided limit whenever that limit exists, which regularity guarantees
--   - encoding: regularity: ψ_D(t) = t − 1/h_D(t) nondecreasing on the support → ψ_D(t) = t − S_D(t)/f(t) monotone on the interior of the support; reason: the endpoint values of ψ_D are one-sided limits of interior values, so monotonicity on the interior is monotonicity on the support
--   - encoding: real expected revenues, suprema and probabilities → nonnegative extended reals (ℝ≥0∞): lintegrals, suprema and measures; reason: the base mission's convention; it represents every finite value unchanged and avoids default-zero integrals
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.13, printed p.38 (PDF p.40); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_Regularity

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Lemma 4.13, p.38 (PDF 40), (62): for a regular magnitude `D` with `r = Rev(D)` and every
`t ≥ 0`, `sup_{0 ≤ p ≤ t} p S(p) ≥ min{r, t}/2`. -/
theorem truncated_regular_revenue (D : Measure ℝ) (hD : RegularMagnitude D) (t : ℝ) (ht : 0 ≤ t) :
    (1 / 2 : ℝ≥0∞) * min (scalarRevenue D) (ENNReal.ofReal t) ≤
      ⨆ (p : ℝ) (_ : 0 ≤ p) (_ : p ≤ t), ENNReal.ofReal p * D (Set.Ici p) := by sorry


end IndependentInfoPricing.Main.Supplement
