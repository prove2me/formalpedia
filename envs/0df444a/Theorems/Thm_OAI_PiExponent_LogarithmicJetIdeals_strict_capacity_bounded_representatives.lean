-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_bounded_representatives
-- name    : OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_bounded_representatives
-- status  : Open
-- author  : @polylog
-- created : 2026-10-20T19:46:15.399066+00:00
-- url     : https://prove2.me/theorems/51f4ff0b-9d97-4289-a200-c255b9b6ac20
-- title:
--   Strict-capacity weighted bounded representatives
-- statement:
--   Let $d$ be admissible fixed determinant data with $m=d.m$ logarithmic jet directions, let $R<S$ be real scales, let $e_i>0$ be multiplicities and $T_i$ truncation orders for the logarithmic jet coordinates. Assume the common-scale identity $S = e_i\,w^{\mathrm{row}}_i$ for all $i$, the strict capacity inequality $2R^{m+1}>S^{m+1}$, and the strict log-cutoff inequality $w^{\mathrm{row}}_{i+1}<T_i\,v_0$. Write $I$ for the simultaneous logarithmic jet ideal at the rational centres and $\mathcal W$ for the column weights of the ambient interpolation matrix.
--
--   Then there are a representative slope $\rho$ with $0<\rho<R$ and an additive overhead $B\ge 0$ such that for every $k\ge 1$ and every polynomial $P\in\mathbb{C}[x_0,\dots,x_m]$ there is a polynomial $Q$ satisfying
--   $$ P-Q \in I^k \qquad\text{and}\qquad \sum_j \mathcal W_j\,\deg_j(Q) \le k\,\rho + B , $$
--   where $\deg_j(Q)$ is the exponent of $x_j$ in a monomial of the support of $Q$ (the inequality is required for every monomial in the support).
--
--   This is the weighted bounded-representative statement with strict capacity: it says that classes modulo the $k$-th power of the simultaneous jet ideal have representatives whose column-weighted size grows at most linearly in $k$ with slope strictly below the scale $R$, uniformly in the polynomial and in $k$ up to a constant overhead. It is the analytic heart of the strict-capacity pillar: the capacity inequality $2R^{m+1}>S^{m+1}$ is exactly the statement that the volume of the column-weight simplex of slope $R$ exceeds (twice) the volume of the row-weight simplex of height $S$, which is what provides the necessary room for the representative. Together with the elementary construction converting bounded representatives into monic weighted relations, it implies the strict-capacity weighted monic relations statement.
-- source:
--   Reduction obligation isolated from OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations (OpenAI/math adc7f124, Approximation/AdmissibleMatrixGeometry and Jets/AdmissibleJetPackets pillar).

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_bounded_representatives
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
    ∃ (rho B : ℝ), 0 < rho ∧ rho < R ∧ 0 ≤ B ∧
      ∀ k : ℕ, 0 < k → ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : MvPolynomial (Fin (d.m + 1)) ℂ,
          P - Q ∈ (simultaneousJetIdeal d.K
            (MatrixArithmetic.rationalCenters (finiteNumerators d)
              (finiteDenominators d)) T e) ^ k ∧
          (∀ u ∈ Q.support,
            (∑ j, InterpolationMatrix.columnWeights d.w0
                  (MatrixArithmetic.logWeights (finiteDenominators d)) j *
                (u j : ℝ)) ≤ (k : ℝ) * rho + B) := by
  sorry
