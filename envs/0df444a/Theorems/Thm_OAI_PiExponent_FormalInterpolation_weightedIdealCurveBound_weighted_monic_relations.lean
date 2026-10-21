-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_weighted_monic_relations
-- name    : OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_weighted_monic_relations
-- status  : Open
-- author  : @polylog
-- created : 2026-10-20T19:21:35.935233+00:00
-- url     : https://prove2.me/theorems/b46347c8-1e1a-4d55-ac28-ac67155cc29b
-- title:
--   Curve-contact bound yields weighted monic relations below any larger rate
-- statement:
--   A uniform weighted curve-contact bound for a finite-colength affine ideal forces the existence of weighted monic relations in its powers, with degree rate arbitrarily close to the contact rate from above.
--
--   Let $I\subseteq\mathbb{C}[X_1,\dots,X_d]$ be an ideal of finite colength, $w_i>0$ rational degree weights, and let $\rho\ge 0$ be a rate such that for every one-dimensional generating curve in function-field form the total contact of $I$ along the curve is at most $\rho$ times the weighted pole degree. Then, for every rational $a>\rho$, there exist:
--   - a positive integer $k$,
--   - positive integers $b_1,\dots,b_d$,
--   - polynomials $F_1,\dots,F_d\in I^k$,
--
--   such that each monic coordinate relation $X_i^{b_i}-F_i$ has all exponents in its support strictly below the weighted degree $w_i b_i$,
--   $$ \sum_j w_j v_j < w_i b_i \qquad \text{for every } v\in\mathrm{supp}(X_i^{b_i}-F_i), $$
--   and the relation degrees satisfy the rate budget
--   $$ w_i\,b_i \le k\,a \qquad (1\le i\le d). $$
--
--   In geometric language, the curve-contact hypothesis controls the weighted Newton polygon of the ideal; the weighted compactification and ampleness (Serre vanishing, ordinary Rees recovery) produce weighted monic relations whose per-power degree cost is at most any prescribed rate strictly larger than $\rho$. The result is the algebraic input needed to bound representatives modulo all powers of $I$.
-- source:
--   Reduction obligation for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_quotient_representatives (globalInterpolation pillar; weighted compactification / ampleness / Serre vanishing / ordinary Rees recovery argument), split at the interface between the geometric weighted-monic-relations output of the curve criterion and the algebraic weighted division step. (geometric step: curve criterion -> weighted monic relations)

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_weighted_monic_relations
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (a : Rat) (ha : rho < a) :
    ∃ k : Nat, 0 < k ∧ ∃ (b : Fin d → Nat), (∀ i, 0 < b i) ∧
      ∃ (F : Fin d → MvPolynomial (Fin d) Complex),
        (∀ i, F i ∈ I ^ k) ∧
        (∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
          (∑ j, (w j : Real) * (v j : Real)) < (w i : Real) * (b i : Real)) ∧
        (∀ i, (w i : Real) * (b i : Real) ≤ (k : Real) * (a : Real)) := by
  sorry
