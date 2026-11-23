-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentProductPMFSumLaw
-- name    : Kyprianou.Ch01.independentProductPMFSumLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:08:31.701896+00:00
-- url     : https://prove2.me/theorems/85a958d5-0816-4540-a348-a20137de905c
-- title:
--   Product-probability sum of almost-everywhere measurable discrete variables has PMF convolution law
-- statement:
--   For two almost-everywhere-measurable natural-number random variables f and g under a common probability measure Q, with given point-mass functions p and q, their independent product-space sum f(ω1)+g(ω2) has mass at k equal to (p.bind (fun n => q.map (fun m => n+m))) k. Prove by taking measurable representatives (AEMeasurable.mk), applying Measure.map_prod_map and map of addition to the product PMF law, then using measure of singleton events. The result is an ordinary general product-measure identity and assumes no branching or offspring moments.
-- source:
--   Mathlib probability measure product construction and PMF monad convolution, applied to Kyprianou (2006) Chapter 1 reverse Lamperti independent ancestor coupling.

import Mathlib
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentProductPMFSumLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f g : Ω → ℕ)
    (hf : AEMeasurable f Q) (hg : AEMeasurable g Q)
    (p q : PMF ℕ)
    (hp : ∀ n : ℕ, Q {ω | f ω = n} = p n)
    (hq : ∀ n : ℕ, Q {ω | g ω = n} = q n)
    (k : ℕ) :
    (Q.prod Q) {z : Ω × Ω | f z.1 + g z.2 = k} =
      ((p.bind (fun n => q.map (fun m => n + m))) k) := by
  sorry
