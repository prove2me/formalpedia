-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_weighted_monic_relations
-- name    : OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations
-- status  : Open
-- author  : @polylog
-- created : 2026-10-20T19:16:01.035705+00:00
-- url     : https://prove2.me/theorems/11f55011-be19-49a6-a0e5-460ed21573e2
-- title:
--   Strict-capacity weighted monic relations below the row scale
-- statement:
--   Under the strict-capacity hypotheses of the row geometry, the simultaneous logarithmic jet ideal admits weighted monic coordinate relations with a slope strictly below $R$.
--
--   Let $d$ be admissible fixed data with dimension $m$, let $R<S$ be real scales, let $e:\mathrm{Fin}(m+1)\to\mathbb{N}$, $T:\mathrm{Fin}\,m\to\mathbb{N}$ be positive multiplicity and truncation data, and assume:
--   $$ S = e_i\cdot w^{\mathrm{row}}_i \quad (0\le i\le m), \qquad 2R^{m+1} > S^{m+1}, \qquad w^{\mathrm{row}}_{i+1} < T_i\,v_0, $$
--   where $w^{\mathrm{row}}$ are the row weights $v_0$ and $\lceil\log q_i\rceil/\theta$, and let
--   $$ I = \mathrm{simultaneousJetIdeal}\bigl(d.K,\ \mathrm{rationalCenters}(d),\ T,\ e\bigr). $$
--   Then there exist a power $k>0$, positive integers $b_0,\dots,b_m$, polynomials $F_0,\dots,F_m\in I^k$, and a real slope $a$ with $0<a<R$ such that for every $i$:
--   $$ \mathrm{supp}\bigl(X_i^{b_i}-F_i\bigr) \text{ is supported strictly below the column weight } w^{\mathrm{col}}_i b_i, $$
--   i.e. every exponent $u$ in that support satisfies
--   $$ \sum_j w^{\mathrm{col}}_j u_j < w^{\mathrm{col}}_i b_i, $$
--   and the degrees fit in the budget
--   $$ w^{\mathrm{col}}_i b_i \le k\,a , $$
--   where $w^{\mathrm{col}} = (d.w_0,\ \lceil\log q_j\rceil)$ are the column weights.
--
--   In other words: the strict capacity inequality forces the existence of a system of weighted monic relations whose normal-form weight cost per ideal power is strictly smaller than the scale $R$. This is the geometric input behind bounded-support representatives for all sufficiently large powers of $I$; the slope budget $a<R$ leaves room to absorb the fixed additive weight overhead of the relations.
-- source:
--   Reduction-specialization of the strict-capacity row-geometry obligations: auxiliary lemma extracted from the same source region as OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_bounded_power_representatives (OpenAI math, commit adc7f124, lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean), intended as the weighted-monic-relations input of the generic normal-form argument.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations
    {nu : ℝ} (d : FixedData nu) (R S : ℝ)
    (e : Fin (d.m + 1) → ℕ) (T : Fin d.m → ℕ)
    (hR : 0 < R) (hRS : R < S)
    (he : ∀ i, 0 < e i)
    (hcommon : ∀ i, S = (e i : ℝ) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
    (hcapacity : 2 * R ^ (d.m + 1 : ℕ) > S ^ (d.m + 1 : ℕ))
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ <
      (T i : ℝ) * (d.v0 : ℝ)) :
    ∃ k : ℕ, 0 < k ∧ ∃ (b : Fin (d.m + 1) → ℕ), (∀ i, 0 < b i) ∧
      ∃ (F : Fin (d.m + 1) → MvPolynomial (Fin (d.m + 1)) ℂ), ∃ a : ℝ,
        0 < a ∧ a < R ∧
        (∀ i, F i ∈ (simultaneousJetIdeal d.K
          (MatrixArithmetic.rationalCenters (finiteNumerators d)
            (finiteDenominators d)) T e) ^ k) ∧
        (∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
          (∑ j, InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) j * (u j : ℝ)) <
            InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i * (b i : ℝ)) ∧
        (∀ i, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i * (b i : ℝ) ≤
            (k : ℝ) * a) := by
  sorry
