-- Prove2me | Theorems.Thm_NeymanPearsonClassification_strengthened_constraint_negative_result
-- name    : NeymanPearsonClassification.strengthened_constraint_negative_result
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:47:08.132617+00:00
-- url     : https://prove2.me/theorems/582315b3-a07e-4388-9bb8-e9371557a962
-- title:
--   Proposition 3.1: with the 0-1 loss, a strengthened type I constraint can cost a fixed excess type II error over the NP oracle
-- statement:
--   Fix $\alpha\in(0,1)$ and a dimension $d\ge1$. There exist base classifiers $h_1,h_2:\mathbb{R}^d\to[-1,1]$ and class-conditional laws $P^-,P^+$ with the following properties. Write $\mathsf h_\lambda=\lambda h_1+(1-\lambda)h_2$, $\lambda\in[0,1]$.
--
--   1. Some $\mathsf h_\lambda$ is negative everywhere, so it has zero type I error and zero empirical type I error. Hence the strengthened problems below are feasible.
--   2. Every $\mathsf h_\lambda$ with $R^-(\mathsf h_\lambda)<\alpha$ satisfies
--   $$R^+(\mathsf h_\lambda)-\min_{\lambda'\in[0,1]:\,R^-(\mathsf h_{\lambda'})\le\alpha}R^+(\mathsf h_{\lambda'})\ge\alpha>0,$$
--   that is, its excess type II error over the NP oracle at level $\alpha$ is at least $\alpha$.
--   3. If $\alpha\le1/2$, then for every sample size $n^-\ge1$ and every i.i.d. sample $X^-_1,\dots,X^-_{n^-}$ from $P^-$, with probability at least $\alpha\wedge\frac14$ the same inequality holds for every $\mathsf h_\lambda$ whose empirical type I error $\hat R^-(\mathsf h_\lambda)=\frac1{n^-}\sum_i\mathbf 1(\mathsf h_\lambda(X^-_i)\ge0)$ is $<\alpha$.
--
--   So with the 0-1 loss, any strengthened type I constraint, empirical or not, can cost a fixed excess type II error of $\alpha$ over the NP oracle, whatever the sample size.
--
--   **Formalization Note** The pair $(h_1,h_2)$ is indexed by $\mathrm{Fin}\,2$, and $[h_1,h_2]$ is the convex hull over the 2-simplex. The reference value is the $\alpha$-constrained minimum $\min_{\lambda':R^-(\mathsf h_{\lambda'})\le\alpha}R^+(\mathsf h_{\lambda'})$, which is what the paper's proof subtracts (Section 6.1) and what its "excess type II risk" sentences refer to. The printed display subtracts the unconstrained $\min_{\lambda\in[0,1]}$; with that reference the existential is satisfied trivially, e.g. by $h_1\equiv-1$, $h_2\equiv1$, which have zero excess over the NP oracle. Item 1 makes explicit the feasibility that the paper's "in particular" consequences (about $h^*(\alpha-\varepsilon_{n^-})$ and $\hat h(\alpha-\varepsilon_{n^-})$) presuppose; without it the existential would also be satisfied by classifiers that never meet the strengthened constraint. The minimum is written as an infimum. The probability claim bounds the (outer) probability of the failure event by $1-\alpha\wedge\frac14$.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750v1 (2011), Section 3.1, Proposition 3.1, eq. (3.3), p. 6; proof in Section 6.1, pp. 13-14 (reference value as subtracted in the proof)

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

theorem strengthened_constraint_negative_result {d : ℕ} (hd : 1 ≤ d) (α : ℝ)
    (hα : α ∈ Set.Ioo 0 1) :
    ∃ (h : Fin 2 → EuclideanSpace ℝ (Fin d) → ℝ) (Pm Pp : Measure (EuclideanSpace ℝ (Fin d))),
      IsBaseFamily h ∧ IsProbabilityMeasure Pm ∧ IsProbabilityMeasure Pp ∧
      (∃ lam ∈ stdSimplex ℝ (Fin 2), ∀ x, convComb h lam x < 0) ∧
      (∀ lam ∈ stdSimplex ℝ (Fin 2), typeI Pm (convComb h lam) < α →
        α ≤ typeII Pp (convComb h lam) -
          sInf ((fun l => typeII Pp (convComb h l)) ''
            {l | l ∈ stdSimplex ℝ (Fin 2) ∧ typeI Pm (convComb h l) ≤ α})) ∧
      (α ≤ 1 / 2 → ∀ nm : ℕ, 1 ≤ nm →
        ∀ (Omega : Type) [MeasurableSpace Omega] (μ : Measure Omega), IsProbabilityMeasure μ →
        ∀ Xm : Fin nm → Omega → EuclideanSpace ℝ (Fin d), (∀ i, Measurable (Xm i)) →
          iIndepFun Xm μ → (∀ i, μ.map (Xm i) = Pm) →
          μ {ω | ¬ ∀ lam ∈ stdSimplex ℝ (Fin 2),
              empTypeI Finset.univ (fun i => Xm i ω) (convComb h lam) < α →
              α ≤ typeII Pp (convComb h lam) -
                sInf ((fun l => typeII Pp (convComb h l)) ''
                  {l | l ∈ stdSimplex ℝ (Fin 2) ∧ typeI Pm (convComb h l) ≤ α})} ≤
            1 - ENNReal.ofReal (min α (1 / 4))) := by sorry

end NeymanPearsonClassification
