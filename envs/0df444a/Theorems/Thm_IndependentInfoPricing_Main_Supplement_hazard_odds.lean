-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_hazard_odds
-- name    : IndependentInfoPricing.Main.Supplement.hazard_odds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:50:15.965842+00:00
-- url     : https://prove2.me/theorems/3ac59db2-1d60-442f-99ca-51fca0376ec0
-- title:
--   Lemma 4.4 — Hazard-odds lemma
-- statement:
--   Let $X\ge0$ be a magnitude in the scope of §4.2, with hazard rate $h_X$, dimensionless hazard $\eta_X(t)=t\,h_X(t)$, and
--   $$c_X(t)=-\psi_X(t)=\frac1{h_X(t)}-t,\qquad \Lambda_X(t)=\frac{\eta_X(t)}{1-\eta_X(t)}.$$
--
--   1. At every point $t>0$ of the interior of the support, $c_X(t)>0$ if and only if $\eta_X(t)<1$.
--   2. On any interval $J$ contained in the interior of the support on which $t>0$ and $c_X(t)>0$, the virtual value $\psi_X$ is nondecreasing on $J$ if and only if $\Lambda_X(t)/t$ is nondecreasing on $J$.
--   3. In particular, if $X$ is regular, then $\Lambda_X(t)/t$ is nondecreasing on every such interval $J$.
--
--   This is the form in which regularity enters the comparison of the relaxations with $\operatorname{Rev}(Z)$ (Corollary 4.5, Lemma 4.6), and the truncated-revenue bound of Lemma 4.13.
--
--   **Formalization Note** "Interval" is an order-connected set of reals. The equivalence in item 2 is stated for every magnitude in scope; regularity is assumed only in item 3.
--
--   Differences from the source:
--   - reading: a continuously differentiable density, positive throughout an interval support, with pointwise values at a finite left endpoint understood as right limits (possibly extended) → a density version f : ℝ → [0,∞] that is finite, positive and C¹ on the interior of the topological support, the support being an interval; the hazard η at the left endpoint is the liminf of t·f(t)/S(t) from the interior; reason: endpoint values are one-sided limits in the source, so positivity is imposed where the density is evaluated pointwise (the interior); the liminf equals the source's one-sided limit whenever that limit exists, which regularity guarantees
--   - encoding: regularity: ψ_D(t) = t − 1/h_D(t) nondecreasing on the support → ψ_D(t) = t − S_D(t)/f(t) monotone on the interior of the support; reason: the endpoint values of ψ_D are one-sided limits of interior values, so monotonicity on the interior is monotonicity on the support
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.4, printed p.28 (PDF p.30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_Regularity

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Lemma 4.4, p.28 (PDF 30): hazard-odds form of regularity on intervals of the interior of the
support where `t > 0` and `c_D(t) > 0`, with the stated equivalence `c_D(t) > 0 ⇔ η_D(t) < 1`. -/
theorem hazard_odds (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (hD : MagnitudeScope D f) :
    (∀ t ∈ interior (lawSupport D), 0 < t → (0 < reverseVirtual D f t ↔ eta D f t < 1)) ∧
    ∀ J : Set ℝ, J.OrdConnected → J ⊆ interior (lawSupport D) → (∀ t ∈ J, 0 < t) →
      (∀ t ∈ J, 0 < reverseVirtual D f t) →
      (MonotoneOn (virtualValue D f) J ↔ MonotoneOn (fun t => hazardOdds D f t / t) J) ∧
      (Regular D f → MonotoneOn (fun t => hazardOdds D f t / t) J) := by sorry


end IndependentInfoPricing.Main.Supplement
