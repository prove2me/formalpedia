-- Prove2me | Theorems.Thm_MeasureTheory_isProbabilityMeasure_mixture
-- name    : MeasureTheory.isProbabilityMeasure_mixture
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T15:10:08.571067+00:00
-- url     : https://prove2.me/theorems/956cd126-7039-4bad-89fd-a21d6d320e3e
-- title:
--   A convex combination of two probability measures is a probability measure
-- statement:
--   Let $Z$ be a measurable space, let $\pi$ and $\rho$ be probability measures on $Z$, and
--   let $a,b\ge 0$ be real numbers with $a+b=1$. Then the mixture
--
--   $$
--   a\pi + b\rho
--   $$
--
--   is again a probability measure on $Z$.
--
--   The statement is the one-line fact that the set of probability measures on a measurable space is
--   convex, in exactly the form a proof needs it: not as a property of a convex set, but as an
--   instance to hand to the next lemma. It appears wherever two laws are interpolated — a coupling
--   argument that mixes a pair of candidate distributions, a worst-case distribution written as a
--   mixture of extreme points, a randomized strategy over two pure ones. Eight accepted proofs in
--   this collection each establish it on their own before using it.
--
--   **Formalization Note.** The scalars multiplying the measures live in `ℝ≥0∞`, so `a` and `b` are
--   coerced with `ENNReal.ofReal` and the mixture is written `ENNReal.ofReal a • π + ENNReal.ofReal b
--   • ρ`. The conclusion is the `IsProbabilityMeasure` instance for that measure; the hypotheses
--   `0 ≤ a`, `0 ≤ b` and `a + b = 1` are what make the total mass one.
-- source:
--   Eight distinct accepted submissions prove this inline, each for itself. Carved from https://prove2.me/submissions/505563a3-50a1-4701-87c6-32f58db20f14, lines 96-106.

import Mathlib

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

theorem MeasureTheory.isProbabilityMeasure_mixture {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (hπ : IsProbabilityMeasure π) (hρ : IsProbabilityMeasure ρ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsProbabilityMeasure (ENNReal.ofReal a • π + ENNReal.ofReal b • ρ) := by sorry
