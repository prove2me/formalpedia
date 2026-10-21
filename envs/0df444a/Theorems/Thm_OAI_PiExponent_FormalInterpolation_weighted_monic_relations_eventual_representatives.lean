-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_monic_relations_eventual_representatives
-- name    : OAI.PiExponent.FormalInterpolation.weighted_monic_relations_eventual_representatives
-- status  : Proved
-- author  : @polylog
-- created : 2026-10-20T19:21:38.545962+00:00
-- url     : https://prove2.me/theorems/fc033a16-0601-4516-9290-53a9f38e9318
-- title:
--   Weighted monic relations yield eventual bounded representatives
-- statement:
--   Weighted monic relations in a power of an ideal produce eventual bounded-support representatives modulo every power of the ideal, with any degree rate above the relations' rate.
--
--   Let $I\subseteq\mathbb{C}[X_1,\dots,X_d]$ be an ideal, $w_i>0$ rational degree weights. Suppose that for some $k>0$ and positive integers $b_1,\dots,b_d$ there are polynomials $F_i\in I^k$ such that every exponent $v$ in the support of the monic relation $X_i^{b_i}-F_i$ satisfies
--   $$ \sum_j w_j v_j < w_i b_i , $$
--   and the relation degrees obey a rate budget
--   $$ w_i b_i \le k\,a \qquad (1\le i\le d) $$
--   for some rational $a>0$. Then for every rational rate $\delta>a$ there is a threshold $n_0$ such that every polynomial $p$ has, for all $n\ge n_0$, a representative $q$ with
--   $$ p-q\in I^n \qquad\text{and}\qquad \sum_i w_i u_i \le n\,\delta \quad (u\in\mathrm{supp}(q)). $$
--
--   The proof is weighted monic division: a monomial $X^u$ whose weighted degree exceeds $n\delta$ has floor cost $\sum_i \lfloor u_i/b_i\rfloor$ exceeding $n/k$, so a product of $n/k$ relations gives an element of $I^n$ agreeing with $X^u$ on its leading monomial and strictly decreasing the weighted degree; well-foundedness of weighted-degree descent then yields remainders supported below weighted degree $n\delta$, and linearity extends the construction from monomials to all polynomials.
-- source:
--   Reduction obligation for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_quotient_representatives (globalInterpolation pillar; weighted compactification / ampleness / Serre vanishing / ordinary Rees recovery argument), split at the interface between the geometric weighted-monic-relations output of the curve criterion and the algebraic weighted division step. (algebraic step: weighted division / Rees recovery)

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_monic_relations_eventual_representatives
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (k : Nat) (hk : 0 < k)
    (b : Fin d → Nat) (hb : ∀ i, 0 < b i)
    (F : Fin d → MvPolynomial (Fin d) Complex)
    (hF : ∀ i, F i ∈ I ^ k)
    (hbelow : ∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
      (∑ j, (w j : Real) * (v j : Real)) < (w i : Real) * (b i : Real))
    (a delta : Rat) (ha0 : 0 < a) (ha : a < delta)
    (hbudget : ∀ i, (w i : Real) * (b i : Real) ≤ (k : Real) * (a : Real)) :
    ∃ n₀ : Nat, ∀ n : Nat, n₀ ≤ n →
      ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ u ∈ q.support,
            ∑ i, (w i : Real) * (u i : Real) ≤ (n : Real) * (delta : Real) := by
  sorry
