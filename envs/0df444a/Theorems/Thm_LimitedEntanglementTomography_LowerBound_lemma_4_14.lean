-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_lemma_4_14
-- name    : LimitedEntanglementTomography.LowerBound.lemma_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:14.466199+00:00
-- url     : https://prove2.me/theorems/115f4d29-1a12-4265-b323-501a04c6b6ff
-- title:
--   Lemma 4.14 — Fano's inequality for metric balls
-- statement:
--   Let $(\mathcal X,\mathrm{dist})$ be a metric space with its Borel $\sigma$-algebra, let $(X,Y)$ have a joint law with $X\sim\pi$ taking values in $\mathcal X$, and let $\hat X(Y)$ be a measurable estimate of $X$ based on $Y$. Let $\eta\ge0$ and $0<\beta<1$. If
--   $$\sup_{x_0\in\mathcal X}\pi\{x:\mathrm{dist}(x,x_0)\le\eta\}\le\beta$$
--   and $q=\Pr[\mathrm{dist}(X,\hat X(Y))\le\eta]$, then
--   $$I(X;Y)\ge q\log\frac1\beta-\log2 .$$
--
--   Logarithms are natural, which gives the additive $\log2$. This turns small prior mass of metric balls into a lower bound on the information any accurate estimate needs.
--
--   Differences from the source:
--   - reading: q = Pr[d(X, X̂(Y)) ≤ η] for a general metric space → hypothesis that the event {dist(X, X̂(Y)) ≤ η} is measurable; reason: the source takes the probability q of this event, which presupposes it is an event; it is automatic for separable spaces (all uses), and assuming it keeps the lemma for every metric space
--   - encoding: I(X;Y) ≥ q log(1/β) − log 2 between real numbers → ofReal(q log(1/β) − log 2) ≤ I(X;Y) in [0,∞]; reason: I(X;Y) ≥ 0, so the truncation of a negative right-hand side to 0 changes nothing, and infinite information is allowed
--   - encoding: probabilities and expectations of nonnegative quantities in ℝ → values of measures in [0,∞] (ENNReal); reason: a probability is the same number; inequalities are unchanged
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §4.4, printed p.17 / PDF p.19, Lemma 4.14 (eq. (30))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Prior

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Lemma 4.14, printed p.17 / PDF p.19, eq. (30).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Lemma 4.14 (Fano's inequality for metric balls).** Let `(X, dist)` be a metric space,
`(X, Y)` jointly distributed with `X ∼ π`, and `X̂(Y)` a measurable estimate. Let `η ≥ 0`,
`0 < β < 1`. If `sup_{x₀} π{x : dist(x, x₀) ≤ η} ≤ β` and `q = Pr[dist(X, X̂(Y)) ≤ η]`, then
`I(X; Y) ≥ q log(1/β) − log 2` (natural logarithms). -/
theorem lemma_4_14 {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] (P : Measure (X × Y)) [IsProbabilityMeasure P] (est : Y → X)
    (hest : Measurable est) (η β : ℝ) (hη : 0 ≤ η) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hball : ∀ x₀ : X, P.fst (Metric.closedBall x₀ η) ≤ ENNReal.ofReal β)
    (hmeas : MeasurableSet {p : X × Y | dist p.1 (est p.2) ≤ η}) :
    ENNReal.ofReal ((P {p : X × Y | dist p.1 (est p.2) ≤ η}).toReal * Real.log (1 / β) - Real.log 2)
      ≤ mutualInfo P := by sorry

end LimitedEntanglementTomography.LowerBound
