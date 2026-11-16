-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_regular_half_tail
-- name    : IndependentInfoPricing.Main.Supplement.regular_half_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:54:36.99529+00:00
-- url     : https://prove2.me/theorems/ee0a4334-82ff-4a84-ad5b-48b6ba7460a9
-- title:
--   Corollary 4.14 — Half-tail at the revenue scale
-- statement:
--   Let $D\ge0$ be a regular magnitude in the scope of §4.4 (positive continuously differentiable density on an interval support, finite monopoly price). Then
--   $$\Pr\bigl(D\ge\operatorname{Rev}(D)\bigr)\ge\frac12.\tag{63}$$
--
--   The threshold is the revenue level $\operatorname{Rev}(D)$, not the monopoly price. This half-tail property is the hypothesis of the aggregate shielding lemma (Lemma 4.16) and of the dimension-independent bound of §4.5; the corollary shows that it holds automatically for every regular branch.
--
--   **Formalization Note** The conclusion is the published `HalfTail D`, i.e. $\Pr(\{x:\operatorname{Rev}(D)\le x\})\ge1/2$ with $\operatorname{Rev}(D)$ compared in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: a continuously differentiable density, positive throughout an interval support, with pointwise values at a finite left endpoint understood as right limits (possibly extended) → a density version f : ℝ → [0,∞] that is finite, positive and C¹ on the interior of the topological support, the support being an interval; the hazard η at the left endpoint is the liminf of t·f(t)/S(t) from the interior; reason: endpoint values are one-sided limits in the source, so positivity is imposed where the density is evaluated pointwise (the interior); the liminf equals the source's one-sided limit whenever that limit exists, which regularity guarantees
--   - encoding: regularity: ψ_D(t) = t − 1/h_D(t) nondecreasing on the support → ψ_D(t) = t − S_D(t)/f(t) monotone on the interior of the support; reason: the endpoint values of ψ_D are one-sided limits of interior values, so monotonicity on the interior is monotonicity on the support
--   - encoding: Pr(D ≥ Rev(D)) ≥ 1/2 → HalfTail D: 1/2 ≤ D{x | Rev(D) ≤ ofReal x}; reason: for Rev(D) > 0 the event is {D ≥ Rev(D)}; for Rev(D) = 0 it differs from {D ≥ 0} only on {D < 0}, a null set because D ≥ 0
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Corollary 4.14, printed p.39 (PDF p.41); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_Regularity

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Corollary 4.14, p.39 (PDF 41), (63): a regular magnitude satisfies `Pr(D ≥ Rev(D)) ≥ 1/2`
(the published `HalfTail`). -/
theorem regular_half_tail (D : Measure ℝ) (hD : RegularMagnitude D) : HalfTail D := by sorry


end IndependentInfoPricing.Main.Supplement
