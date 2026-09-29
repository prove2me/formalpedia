-- Prove2me | Theorems.Thm_InformationTheory_finite_range_mutualInformation_le_marginal_entropy
-- name    : InformationTheory.finite_range_mutualInformation_le_marginal_entropy
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T23:57:14.704574+00:00
-- url     : https://prove2.me/theorems/08a4998c-a576-4e92-a01b-ff89e32284f6
-- title:
--   Mutual information is at most marginal entropy
-- statement:
--   Let $X$ and $Y$ be random variables on a common probability space, with $Y$ taking values in the finite set $[k]$. If $p_a=\mathbb P(Y=a)$, then
--
--   $$
--   I(X;Y)
--   =D\!\left(P_{(X,Y)}\,\middle\|\,P_X\otimes P_Y\right)
--   \le H(Y)
--   =\sum_{a\in[k]} -p_a\log p_a.
--   $$
--
--   This is the standard fact that observing $X$ cannot reveal more information about $Y$ than the entropy initially present in $Y$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), https://tor-lattimore.com/downloads/book/book.pdf, printed p. 471 (PDF p. 480), proof of Theorem 36.5: information learned about the optimal action is bounded by its entropy; the entropy is then bounded by log k.

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators

theorem InformationTheory.finite_range_mutualInformation_le_marginal_entropy
    {Omega Alpha : Type} {mOmega : MeasurableSpace Omega}
    {mAlpha : MeasurableSpace Alpha} {k : ℕ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega → Alpha) (g : Omega → Fin k)
    (hf : Measurable f) (hg : Measurable g) :
    (klDiv (Measure.map (fun x ↦ (f x, g x)) mu)
      ((Measure.map f mu).prod (Measure.map g mu))).toReal ≤
      ∑ a, Real.negMulLog ((Measure.map g mu).real {a}) := by
  sorry
