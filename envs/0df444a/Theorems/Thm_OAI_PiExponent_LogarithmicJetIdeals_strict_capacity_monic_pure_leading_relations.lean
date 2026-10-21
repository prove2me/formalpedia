-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_monic_pure_leading_relations
-- name    : OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_monic_pure_leading_relations
-- status  : Open
-- author  : @polylog
-- created : 2026-10-20T19:56:55.224997+00:00
-- url     : https://prove2.me/theorems/7ccee3aa-3287-4af3-be5c-a88da33f8435
-- title:
--   Strict-capacity initial monic relations
-- statement:
--   Let $d$ be admissible fixed determinant data, with $m=d.m$, and let $R<S$ be real scales, $e_i>0$ multiplicities and $T_i$ truncation orders satisfying the common-scale identity $S=e_i\,w^{\mathrm{row}}_i$, the strict capacity inequality $2R^{m+1}>S^{m+1}$, and the log-cutoff inequalities $w^{\mathrm{row}}_{i+1}<T_i\,v_0$. Write $I$ for the simultaneous logarithmic jet ideal at the rational centres and $\mathcal{W}$ for the column weights.
--
--   Then there exist a slope $\rho$ with $0<\rho<R$, a positive power $k\ge1$, a monomial order $o$, positive integers $b_0,\dots,b_m$ and polynomials $F_0,\dots,F_m\in I^k$ such that, for every $i$, $F_i$ is monic with pure leading power $x_i^{b_i}$ with respect to $o$, the column weight of that pivot is bounded by the capacity budget,
--   $$ \mathcal{W}_i\,b_i \;\le\; k\,\rho , $$
--   and the difference $x_i^{b_i}-F_i$ is supported strictly below the pivot weight,
--   $$ \sum_j \mathcal{W}_j\,u_j \;<\; \mathcal{W}_i\,b_i \qquad\text{for every } u\in\operatorname{supp}(x_i^{b_i}-F_i). $$
--
--   These are the initial monic relations of the strict-capacity layer: monic relations in every logarithmic direction whose pivot degree grows with the power of the jet ideal at a rate strictly below the scale $R$, with all lower terms confined below the pivot in the column-weight order. They are the input of the weighted monic-relation division theory, which converts them into weighted representatives of every residue class modulo $I^n$ with rate $\rho$ and a fixed additive overhead; in particular they imply that for every $k$ every polynomial has a representative modulo $I^k$ of column weight at most $k\rho+B$ for a constant $B$. The existence of such relations is exactly the strict-capacity content of the global-generation argument for the blowup ideal.
-- source:
--   Reduction obligation isolated from OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_bounded_representatives (OpenAI/math adc7f124, Approximation/AdmissibleMatrixGeometry and Jets/AdmissibleJetPackets pillar).

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_monic_pure_leading_relations
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
    ∃ rho : ℝ, 0 < rho ∧ rho < R ∧
      ∃ k : ℕ, 0 < k ∧ ∃ o : MonomialOrder (Fin (d.m + 1)),
        ∃ b : Fin (d.m + 1) → ℕ, (∀ i, 0 < b i) ∧
          ∃ F : Fin (d.m + 1) → MvPolynomial (Fin (d.m + 1)) ℂ,
            (∀ i, F i ∈ (simultaneousJetIdeal d.K
              (MatrixArithmetic.rationalCenters (finiteNumerators d)
                (finiteDenominators d)) T e) ^ k) ∧
            (∀ i, o.leadingCoeff (F i) = 1) ∧
            (∀ i, o.degree (F i) = Finsupp.single i (b i)) ∧
            (∀ i, InterpolationMatrix.columnWeights d.w0
                  (MatrixArithmetic.logWeights (finiteDenominators d)) i *
                (b i : ℝ) ≤ (k : ℝ) * rho) ∧
            (∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
              (∑ j, InterpolationMatrix.columnWeights d.w0
                    (MatrixArithmetic.logWeights (finiteDenominators d)) j *
                  (u j : ℝ)) <
                InterpolationMatrix.columnWeights d.w0
                  (MatrixArithmetic.logWeights (finiteDenominators d)) i *
                (b i : ℝ)) := by
  sorry
