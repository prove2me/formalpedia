-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_single_direction_relaxations
-- name    : IndependentInfoPricing.Main.Supplement.single_direction_relaxations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:49:40.904202+00:00
-- url     : https://prove2.me/theorems/79144f06-1fdc-4809-8216-2695590ab0be
-- title:
--   Lemma 4.3 — Single-direction relaxations
-- statement:
--   Let $X,Y\ge0$ be independent regular magnitudes in the scope of §4.2 (positive continuously differentiable densities on interval supports, finite monopoly prices). A type is $(x,-y)$ with $x,y\ge0$; a menu option $(a,b,p)$ with $a,b\in[0,1]$ gives it utility $xa-yb-p$; the participation constraints are $u\ge0$ (IR$_0$) and $u\ge x-y$ (IR$_1$). Let $\mathrm{OPT}_{\mathrm{rel}}$ be the value of the program with ordinary IC between all types and both participation constraints, and put
--   $$\operatorname{Rel}_X=\mathbb E[H_X(Y)],\qquad \operatorname{Rel}_Y=\mathbb E[H_Y(X)].$$
--   Then:
--
--   1. the relaxation keeping only the IC constraints within each slice of fixed $y$, together with IR$_0$ and IR$_1$ for every type, has value exactly $\operatorname{Rel}_X$; keeping instead the IC constraints within each slice of fixed $x$ gives exactly $\operatorname{Rel}_Y$; in particular
--   $$\mathrm{OPT}_{\mathrm{rel}}\le\min\{\operatorname{Rel}_X,\operatorname{Rel}_Y\};\tag{46}$$
--   2. $H_X$ and $H_Y$ are nondecreasing and concave on $[0,\infty)$, and
--   $$\operatorname{Rel}_X=\int_0^\infty (H_X)'(t)\,S_Y(t)\,dt,\qquad \operatorname{Rel}_Y=\int_0^\infty (H_Y)'(t)\,S_X(t)\,dt;\tag{47}$$
--   3. with the smallest monopoly prices $p^0_X,p^0_Y$,
--   $$\operatorname{Rel}_X=\int_0^{p^0_X}\rho_X'(t)\,S_Y(t)\,dt,\qquad \operatorname{Rel}_Y=\int_0^{p^0_Y}\rho_Y'(t)\,S_X(t)\,dt.\tag{48}$$
--
--   The two slice relaxations are the upper-bound tools of the two-item theorem (Theorem 4.1).
--
--   **Formalization Note** The mechanisms are the base `DirectMechanism (Fin 2)` restricted to the quadrant of types $(x,-y)$, $x,y\ge0$, with measurable allocation and price and nonnegative prices, as in the base model of §2; $\mathrm{OPT}_{\mathrm{rel}}$ is `optRelOn quadrant` on the law of $(X,-Y)$, which is at least the base `optRel` over all of $\mathbb R^2$. Derivatives are Mathlib's `deriv`, whose junk value $0$ at non-differentiability points affects only a null set; the integrals are lintegrals of the (almost everywhere nonnegative) integrands.
--
--   Differences from the source:
--   - reading: a continuously differentiable density, positive throughout an interval support, with pointwise values at a finite left endpoint understood as right limits (possibly extended) → a density version f : ℝ → [0,∞] that is finite, positive and C¹ on the interior of the topological support, the support being an interval; the hazard η at the left endpoint is the liminf of t·f(t)/S(t) from the interior; reason: endpoint values are one-sided limits in the source, so positivity is imposed where the density is evaluated pointwise (the interior); the liminf equals the source's one-sided limit whenever that limit exists, which regularity guarantees
--   - encoding: regularity: ψ_D(t) = t − 1/h_D(t) nondecreasing on the support → ψ_D(t) = t − S_D(t)/f(t) monotone on the interior of the support; reason: the endpoint values of ψ_D are one-sided limits of interior values, so monotonicity on the interior is monotonicity on the support
--   - encoding: derivatives understood almost everywhere and Lebesgue integrals over (0,∞) and (0,p⁰) → Mathlib deriv (value 0 where not differentiable) inside lintegrals of ENNReal.ofReal of the integrand; reason: non-differentiability points form a null set and the integrands are almost everywhere nonnegative, so the integrals are the same
--   - encoding: menu programs over the types (x,−y) with options (a,b,p) → base direct mechanisms on the quadrant {x ≥ 0, −y ≤ 0} with measurable allocation and price and nonnegative prices; reason: the revelation principle form of the same program, with the base model's ex-ante nonnegative prices and the measurability expected revenue needs
--   - encoding: real expected revenues, suprema and probabilities → nonnegative extended reals (ℝ≥0∞): lintegrals, suprema and measures; reason: the base mission's convention; it represents every finite value unchanged and avoids default-zero integrals
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.3, printed p.24 (PDF p.26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_TwoItem

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Lemma 4.3, pp.24–25 (PDF 26–27): exact values of the two slice relaxations, (46), the
monotonicity/concavity of `H_X, H_Y`, and the integral forms (47) and (48). -/
theorem single_direction_relaxations (X Y : Measure ℝ)
    (hX : RegularMagnitude X) (hY : RegularMagnitude Y) :
    sliceValue true (twoItemLaw X Y) = relValue X Y ∧
    sliceValue false (twoItemLaw X Y) = relValue Y X ∧
    optRelOn quadrant (twoItemLaw X Y) ≤ min (relValue X Y) (relValue Y X) ∧
    (MonotoneOn (cappedRevenue X) (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) (cappedRevenue X)) ∧
    (MonotoneOn (cappedRevenue Y) (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) (cappedRevenue Y)) ∧
    relValue X Y = ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (deriv (cappedRevenue X) t * survival Y t) ∧
    relValue Y X = ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (deriv (cappedRevenue Y) t * survival X t) ∧
    relValue X Y = ∫⁻ t in Set.Ioo 0 (monopolyPrice X),
      ENNReal.ofReal (deriv (revenueCurve X) t * survival Y t) ∧
    relValue Y X = ∫⁻ t in Set.Ioo 0 (monopolyPrice Y),
      ENNReal.ofReal (deriv (revenueCurve Y) t * survival X t) := by sorry


end IndependentInfoPricing.Main.Supplement
