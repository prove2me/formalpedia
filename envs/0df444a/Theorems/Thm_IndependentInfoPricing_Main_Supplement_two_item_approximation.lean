-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_two_item_approximation
-- name    : IndependentInfoPricing.Main.Supplement.two_item_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:52:26.82559+00:00
-- url     : https://prove2.me/theorems/12edb07b-350d-44f2-86c4-cdaae4a314de
-- title:
--   Theorem 4.1 — Two-item approximation
-- statement:
--   Let $X,Y\ge0$ be independent and regular, with continuously differentiable densities on interval supports on which the densities are positive, and with finite monopoly prices. Consider the information-pricing instance with two states whose normalized payoff vector is $v=(X,-Y)$, and put $Z=\min\{X,Y\}$. Then
--   $$\mathrm{OPT}\le3\cdot\operatorname{Rev}(Z)=3\cdot\mathrm{FRev}.$$
--
--   Here $\mathrm{OPT}$ is the optimal revenue over all information-pricing mechanisms (all response rules, both free outside options), $\operatorname{Rev}(Z)=\sup_{p\ge0}p\Pr(Z\ge p)$, and $\mathrm{FRev}$ is the revenue of priced full revelation. Section 3 shows that without distributional assumptions the ratio $\mathrm{OPT}/\widetilde R$ is unbounded even for two opposite-sign coordinates; regularity of the two magnitudes restores a constant guarantee.
--
--   **Formalization Note** The instance is the base `oppositeLaw X Y` (coordinate 0 has the law of $X$, coordinate 1 the law of $-Y$); $\mathrm{OPT}$ is the base `opt` and $\mathrm{FRev}$ the base `fullRev`. Both equalities and the inequality are stated.
--
--   Differences from the source:
--   - reading: a continuously differentiable density, positive throughout an interval support, with pointwise values at a finite left endpoint understood as right limits (possibly extended) → a density version f : ℝ → [0,∞] that is finite, positive and C¹ on the interior of the topological support, the support being an interval; the hazard η at the left endpoint is the liminf of t·f(t)/S(t) from the interior; reason: endpoint values are one-sided limits in the source, so positivity is imposed where the density is evaluated pointwise (the interior); the liminf equals the source's one-sided limit whenever that limit exists, which regularity guarantees
--   - encoding: regularity: ψ_D(t) = t − 1/h_D(t) nondecreasing on the support → ψ_D(t) = t − S_D(t)/f(t) monotone on the interior of the support; reason: the endpoint values of ψ_D are one-sided limits of interior values, so monotonicity on the interior is monotonicity on the support
--   - encoding: real expected revenues, suprema and probabilities → nonnegative extended reals (ℝ≥0∞): lintegrals, suprema and measures; reason: the base mission's convention; it represents every finite value unchanged and avoids default-zero integrals
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Theorem 4.1, printed p.22 (PDF p.24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_TwoItem

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Theorem 4.1, p.22 (PDF 24): two-item approximation, `OPT ≤ 3·Rev(Z) = 3·FRev`. -/
theorem two_item_approximation (X Y : Measure ℝ)
    (hX : RegularMagnitude X) (hY : RegularMagnitude Y) :
    opt (twoItemLaw X Y) ≤ 3 * scalarRevenue (minLaw X Y) ∧
    scalarRevenue (minLaw X Y) = fullRev (twoItemLaw X Y) := by sorry


end IndependentInfoPricing.Main.Supplement
