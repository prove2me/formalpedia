-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_weighted_representatives_of_scale
-- name    : OAI.PiExponent.FormalInterpolation.eventual_weighted_representatives_of_scale
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T06:29:17.377691+00:00
-- url     : https://prove2.me/theorems/55f93db8-c671-431a-90e8-4362a11a1c7c
-- title:
--   Eventual weighted representatives at a fixed admissible scale
-- statement:
--   Fix a parameter $\\nu>2$, an admissible determinant family $d$, and scale data $R,T_i,e_i$ satisfying the positivity, row-weight bounds, and scale equalities in the hypotheses. For all sufficiently large $n$, every complex polynomial $P$ in the $d.m+1$ variables has a representative $Q$ of weighted degree at most $nR$ in its class modulo the $n$-th power of the product logarithmic center ideal at the rational centers of $d$. The threshold is uniform over $P$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Ampleness/AdmissibleBlowupGeometry.lean (centerIdeal_restrict and affinePolynomialIdeal); Jets/AdmissibleJetSurjectivity.lean (eventual_jetRestriction_surjective); Jets/AffineJetPolynomial.lean (polynomialQuotient_surjective_of_jetRestriction); Approximation/WeightedGlobalSectionBound.lean (eventual_admissible_supportBound).

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.eventual_weighted_representatives_of_scale
    (nu : ℝ) (hnu : 2 < nu) (d : FixedData nu)
    (R : ℚ) (T : Fin d.m → ℕ) (e : Fin (d.m + 1) → ℕ)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : ℝ) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : ℝ) = (e i : ℝ) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∀ᶠ n : ℕ in atTop,
      ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : FormalInterpolation.WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ)),
          P - Q.val ∈ FormalInterpolation.logarithmicCentersIdeal
            (fun j : Fin d.K => fun i => (j.val : ℂ) *
              MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
            T e ^ n := by sorry
