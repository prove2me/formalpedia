-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_degree_budget
-- name    : OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_degree_budget
-- status  : Proved
-- author  : @polylog
-- created : 2026-10-20T19:37:26.828482+00:00
-- url     : https://prove2.me/theorems/c3df9df8-2ea8-404a-9c8f-fd9b86f843c4
-- title:
--   Strict-capacity degree budget below the row scale
-- statement:
--   Under the strict-capacity row-geometry hypotheses, the column degrees admit a positive slope strictly below the scale $R$ that fits a linear degree budget in the power of the jet ideal.
--
--   Let $d$ be admissible fixed data, let $R<S$ be real scales, $e_i>0$ multiplicity data and $T_i$ truncation orders such that
--   $$ S=e_i\,w^{\mathrm{row}}_i,\qquad 2R^{m+1}>S^{m+1},\qquad w^{\mathrm{row}}_{i+1}<T_i\,v_0, $$
--   where $w^{\mathrm{row}}$ are the row weights. Then there exist a power $k>0$, positive integers $b_0,\dots,b_m$ and a real slope $a$ with
--   $$ 0<a<R\qquad\text{and}\qquad w^{\mathrm{col}}_i b_i\le k\,a\quad(1\le i\le d.m+1), $$
--   where $w^{\mathrm{col}}$ are the column weights.
--   This is the numerical strict-capacity count: the capacity inequality leaves room, below the scale $R$, to choose degrees whose total weighted cost grows at most linearly in the power $k$, with slope strictly smaller than $R$.
-- source:
--   Reduction obligation for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_weighted_monic_relations (the isolated strict-capacity leaf of the pi-exponent mission): split into the algebraic weighted-monic-relations construction and the numerical strict-capacity degree budget. Origin: OpenAI math, commit adc7f124, lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44 (weighted compactification/global section bound), as formalized in the mission's determinant-contradiction tree. (numerical strict-capacity step)

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_degree_budget
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
      ∃ a : ℝ, 0 < a ∧ a < R ∧
        (∀ i, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i * (b i : ℝ) ≤
            (k : ℝ) * a) := by
  sorry
