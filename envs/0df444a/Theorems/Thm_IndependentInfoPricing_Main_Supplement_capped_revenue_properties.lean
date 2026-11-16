-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_capped_revenue_properties
-- name    : IndependentInfoPricing.Main.Supplement.capped_revenue_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:48:57.429211+00:00
-- url     : https://prove2.me/theorems/e3470388-163a-44e6-9435-88a346814c67
-- title:
--   Lemma 4.2 — Properties of the truncated revenue function
-- statement:
--   Let $D\ge0$ be a magnitude in the scope of §4.2: it has a density that is positive and continuously differentiable on the interior of its interval support, a finite monopoly price, and it is **regular** (its virtual value $\psi_D(t)=t-1/h_D(t)$ is nondecreasing). Let $H_D(z)=\sup_{0\le t\le z}t\,S_D(t)$ be its capped revenue. Then on $[0,\infty)$:
--
--   1. $H_D$ is nondecreasing and concave;
--   2. $H_D$ is locally absolutely continuous;
--   3. $H_D(0)=0$ and $0\le H_D(z)\le z$ for every $z\ge0$.
--
--   The concavity of $H_D$ is what allows a Jensen comparison between a random price threshold and a deterministic posted price in the single-direction relaxations (Lemma 4.3).
--
--   **Formalization Note** Local absolute continuity is Mathlib's `AbsolutelyContinuousOnInterval` on every compact interval $[a,b]\subseteq[0,\infty)$. The finite monopoly price is the standing assumption of §4.1.
--
--   Differences from the source:
--   - reading: a continuously differentiable density, positive throughout an interval support, with pointwise values at a finite left endpoint understood as right limits (possibly extended) → a density version f : ℝ → [0,∞] that is finite, positive and C¹ on the interior of the topological support, the support being an interval; the hazard η at the left endpoint is the liminf of t·f(t)/S(t) from the interior; reason: endpoint values are one-sided limits in the source, so positivity is imposed where the density is evaluated pointwise (the interior); the liminf equals the source's one-sided limit whenever that limit exists, which regularity guarantees
--   - encoding: regularity: ψ_D(t) = t − 1/h_D(t) nondecreasing on the support → ψ_D(t) = t − S_D(t)/f(t) monotone on the interior of the support; reason: the endpoint values of ψ_D are one-sided limits of interior values, so monotonicity on the interior is monotonicity on the support
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.2, printed p.23 (PDF p.25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_Regularity

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Lemma 4.2, p.23 (PDF 25): the capped revenue `H_D` of a regular magnitude in the §4.2 scope. -/
theorem capped_revenue_properties (D : Measure ℝ) (hD : RegularMagnitude D) :
    MonotoneOn (cappedRevenue D) (Set.Ici 0) ∧
    ConcaveOn ℝ (Set.Ici 0) (cappedRevenue D) ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval (cappedRevenue D) a b) ∧
    cappedRevenue D 0 = 0 ∧
    ∀ z : ℝ, 0 ≤ z → 0 ≤ cappedRevenue D z ∧ cappedRevenue D z ≤ z := by sorry


end IndependentInfoPricing.Main.Supplement
