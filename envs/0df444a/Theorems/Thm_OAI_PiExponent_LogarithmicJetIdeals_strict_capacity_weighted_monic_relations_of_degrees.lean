-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_weighted_monic_relations_of_degrees
-- name    : OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations_of_degrees
-- status  : Open
-- author  : @polylog
-- created : 2026-10-20T19:37:25.016732+00:00
-- url     : https://prove2.me/theorems/555cb771-405e-4830-ab15-94aa1e828c81
-- title:
--   Weighted monic relations for prescribed coordinate degrees
-- statement:
--   For the simultaneous logarithmic jet ideal of an admissible family, every prescribed system of positive coordinate degrees admits weighted monic relations whose remainders are supported strictly below the corresponding weighted degrees.
--
--   Let $d$ be admissible fixed data with column weights $w_i$ ($1\le i\le d.m+1$), let $T_i$ be truncation orders, $e_i>0$ multiplicity data, and let
--   $$ I=\mathrm{simultaneousJetIdeal}\bigl(d.K,\ \mathrm{rationalCenters}(d),\ T,\ e\bigr). $$
--   For every positive integer $k$ and every choice of positive integers $b_0,\dots,b_m$ there are polynomials $F_0,\dots,F_m\in I^k$ such that each monic coordinate relation $X_i^{b_i}-F_i$ has all exponents in its support strictly below the weighted degree $w_i b_i$:
--   $$ \sum_j w_j u_j < w_i b_i\qquad\text{for every }u\in\operatorname{supp}(X_i^{b_i}-F_i). $$
--   This is the algebraic construction obligation behind bounded representatives for powers of $I$: the monic relations are produced from the interpolation/CRT structure of the logarithmic jet ideals (interpolation of formal jets at the $K$ centers, jet box localization, and exact interpolation of coefficient functionals), after which weighted monic division controls the remainder support.
-- source:
--   Reduction obligation for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations (the isolated strict-capacity leaf of the pi-exponent mission): split into the algebraic weighted-monic-relations construction and the numerical strict-capacity degree budget. Origin: OpenAI math, commit adc7f124, lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44 (weighted compactification/global section bound), as formalized in the mission's determinant-contradiction tree. (algebraic construction step)

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations_of_degrees
    {nu : ℝ} (d : FixedData nu)
    (e : Fin (d.m + 1) → ℕ) (T : Fin d.m → ℕ)
    (k : ℕ) (hk : 0 < k) (b : Fin (d.m + 1) → ℕ) (hb : ∀ i, 0 < b i) :
    ∃ (F : Fin (d.m + 1) → MvPolynomial (Fin (d.m + 1)) ℂ),
      (∀ i, F i ∈ (simultaneousJetIdeal d.K
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T e) ^ k) ∧
      (∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
        (∑ j, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) j * (u j : ℝ)) <
          InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) i * (b i : ℝ)) := by
  sorry
