-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_weighted_representatives_mod_logarithmic_ideal
-- name    : OAI.PiExponent.FormalInterpolation.eventual_weighted_representatives_mod_logarithmic_ideal
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T06:13:19.825184+00:00
-- url     : https://prove2.me/theorems/89c9a7c5-f2df-446d-a5c8-5e48bef6310a
-- title:
--   Eventual weighted polynomial representatives modulo logarithmic center ideal powers
-- statement:
--   For $\nu>2$ and an admissible determinant family $d$, there exist a positive rational radius $R$, fixed logarithm cutoffs $T_i$, and positive integer coordinate powers $e_i$, compatible with the row weights $v=(v_0,w_i/\theta)$:
--   $$v_{i+1}\le T_i v_0,\qquad R=e_i v_i.$$
--   Let $I$ be the product of the logarithmic coordinate-power ideals at the rational centers of $d$. At every sufficiently large natural multiple $H=nR$, every polynomial has a representative of column weight at most $H$ in its class modulo $I^n$:
--   $$\forall P\ \exists Q:\quad \operatorname{wt}_{\mathrm{col}}(\operatorname{supp}Q)\le nR,\qquad P-Q\in I^n.$$
--   The radius, cutoffs, coordinate powers, and eventual threshold are independent of $P$. This is the geometric obligation: choose the weighted scale, lift each affine quotient class through the global jet restriction map, and use the eventual bound on the affine coefficient polynomial of a section. It must be proved from the blowup geometry and section bounds, independently of eventual packet interpolation and packet right inverses.
--
--   **Formalization Note.** This adapted affine consequence combines the cited geometric results; it does not claim that the source already contains this exact standalone declaration.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/WeightedGeometryScale.lean, Scale and chooseScale; Ampleness/AdmissibleBlowupGeometry.lean, scale, centerIdeal_restrict and affinePolynomialIdeal; Jets/AdmissibleJetSurjectivity.lean, eventual_jetRestriction_surjective; Jets/AffineJetPolynomial.lean, polynomialQuotient_surjective_of_jetRestriction; Approximation/WeightedGlobalSectionBound.lean, eventual_admissible_supportBound.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.eventual_weighted_representatives_mod_logarithmic_ideal
    (nu : ℝ) (hnu : 2 < nu) (d : FixedData nu) :
    ∃ (R : ℚ) (T : Fin d.m → ℕ) (e : Fin (d.m + 1) → ℕ),
      0 < R ∧ (∀ i, 0 < e i) ∧
      (∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
        (T i : ℝ) * InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) 0) ∧
      (∀ i, (R : ℝ) = (e i : ℝ) *
        InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
          ∃ Q : FormalInterpolation.WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ)),
            P - Q.val ∈ FormalInterpolation.logarithmicCentersIdeal
              (fun j : Fin d.K => fun i => (j.val : ℂ) *
                MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
              T e ^ n := by sorry
