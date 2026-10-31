-- Prove2me | Theorems.Thm_GMFGLearn_eq_39
-- name    : GMFGLearn.eq_39
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:20.900804+00:00
-- url     : https://prove2.me/theorems/1ad094ee-f196-4d2f-b783-d4e259864618
-- title:
--   (39) — $W_1\le\operatorname{diam}(\mathcal X)d_{TV}=\frac{\operatorname{diam}(\mathcal X)}2\|\nu-\nu'\|_1\le\frac{\operatorname{diam}(\mathcal X)\sqrt{|\mathcal X|}}2\|\nu-\nu'\|_2$ on a finite set
-- statement:
--   Let $\mathcal X$ be a finite metric space and $\nu,\nu'$ probability distributions on $\mathcal X$, viewed as vectors of length $|\mathcal X|$. Then
--
--   $$
--   W_1(\nu,\nu')\le\operatorname{diam}(\mathcal X)\,d_{TV}(\nu,\nu')=\frac{\operatorname{diam}(\mathcal X)}{2}\|\nu-\nu'\|_1\le\frac{\operatorname{diam}(\mathcal X)\sqrt{|\mathcal X|}}{2}\|\nu-\nu'\|_2 .
--   $$
--
--   It converts the $\ell_2$ bounds of Lemmas 6 and 7 on probability vectors into $W_1$ bounds on policies.
--
--   Differences from the source:
--   - generalization: a finite set X ⊆ ℝ^k with the Euclidean distance → a finite metric space with its Borel σ-field; reason: a finite subset of ℝ^k with ‖·‖₂ is a finite metric space, so the source's case is an instance
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, (39), p.21

import Mathlib
import Definitions.Def_GMFGLearn_Distances
import Definitions.Def_GMFGLearn_Smoothing

open MeasureTheory

namespace GMFGLearn

/-- **`W₁ ≤ diam(X) d_TV = diam(X)/2 ‖ν − ν′‖₁ ≤ diam(X)√|X|/2 ‖ν − ν′‖₂` on a finite set (39).**
Guo–Hu–Xu–Zhang, *A General Framework for Learning Mean-Field Games*, arXiv:2003.06069v3, (39),
p.21: "for a finite set X ⊆ ℝ^k and any two (discrete) distributions ν, ν′ over X, we have
W1(ν,ν′) ≤ diam(X)dTV(ν,ν′) = diam(X)/2 ‖ν − ν′‖1 ≤ diam(X)√|X|/2 ‖ν − ν′‖2, where in computing the
ℓ1-norm, ν, ν′ are viewed as vectors of length |X|."

**Formalization Note** `X` is a finite metric space with its Borel σ-algebra (a finite subset of
`ℝ^k` with the Euclidean distance is one); `W₁` has cost `dist`; `diam(X)` is `Metric.diam univ`. All
three relations are stated. -/
theorem eq_39 {X : Type*} [MetricSpace X] [Fintype X] [MeasurableSpace X] [BorelSpace X]
    (ν ν' : ProbabilityMeasure X) :
    W1 (dist : X → X → ℝ) ν ν' ≤ Metric.diam (Set.univ : Set X) * dTV ν ν' ∧
      Metric.diam (Set.univ : Set X) * dTV ν ν' =
        Metric.diam (Set.univ : Set X) / 2 *
          ∑ x, |(ν : Measure X).real {x} - (ν' : Measure X).real {x}| ∧
      Metric.diam (Set.univ : Set X) / 2 *
          ∑ x, |(ν : Measure X).real {x} - (ν' : Measure X).real {x}| ≤
        Metric.diam (Set.univ : Set X) * Real.sqrt (Fintype.card X) / 2 *
          l2 (fun x => (ν : Measure X).real {x} - (ν' : Measure X).real {x}) := by sorry

end GMFGLearn
