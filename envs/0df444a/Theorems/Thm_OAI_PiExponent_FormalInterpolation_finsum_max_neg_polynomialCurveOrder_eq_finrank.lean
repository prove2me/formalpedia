-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finsum_max_neg_polynomialCurveOrder_eq_finrank
-- name    : OAI.PiExponent.FormalInterpolation.finsum_max_neg_polynomialCurveOrder_eq_finrank
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:16:47.169874+00:00
-- url     : https://prove2.me/theorems/72be7d3e-972d-44e2-89ea-dbd6f919a80d
-- title:
--   Pole mass of a transcendental equals $[E:\mathbb{C}(x)]$
-- statement:
--   Let $E/\mathbb{C}$ be a field extension and let $x\in E$ be transcendental over $\mathbb{C}$ with $E$ finite-dimensional over $\mathbb{C}(x)$. Then the finsum over all polynomial curve places of $\max(-\operatorname{ord}_\nu(x),0)$ equals the module rank $[E:\mathbb{C}(x)]$ (as a real number). This is the Place-level identity $\sum_{\operatorname{ord}(x)<0}(-\operatorname{ord} x)=[E:\mathbb{C}(x)]$ transported across the PolynomialCurvePlace $\leftrightarrow$ Place correspondence.
-- source:
--   Mission d7ce6393 FormalInterpolation AG chain; cf. AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open IntermediateField
open OAI.PiExponent.FormalInterpolation
open AlgebraicCurve

theorem OAI.PiExponent.FormalInterpolation.finsum_max_neg_polynomialCurveOrder_eq_finrank
    {E : Type} [Field E] [Algebra Complex E]
    (x : E) (hx : Transcendental Complex x)
    (hfin : FiniteDimensional (IntermediateField.adjoin Complex ({x} : Set E)) E) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (-(polynomialCurveOrder nu x : Real)) 0) =
      (Module.finrank (IntermediateField.adjoin Complex ({x} : Set E)) E : Real) := by sorry
