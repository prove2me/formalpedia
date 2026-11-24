-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_Supplement_theorem82
-- name    : NegativeDP.EssFinite.Supplement.theorem82
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:02:36.721835+00:00
-- url     : https://prove2.me/theorems/7ec35475-cf04-4abe-8128-2dc94bd6e17f
-- title:
--   Theorem 8.2 (D, P) — v* satisfies the optimality equation; unique bounded solution (D), smallest non-negative solution (P)
-- statement:
--   In the discounted and in the positive bounded case the optimal return satisfies the optimality equation
--
--   $$
--   v^*(s)=\sup_a T_av^*(s)\qquad\text{for all }s\in S,
--   $$
--
--   where $T_a$ is the operator of the constant rule $f\equiv a$. In fact:
--
--   1. in the discounted case $v^*$ is the unique bounded solution: every bounded $w$ for which each $T_aw(s)$ is defined and $w=\sup_aT_aw$ equals $v^*$;
--   2. in the positive bounded case $v^*$ is the smallest non-negative solution: every $w\ge0$ for which each $T_aw(s)$ is defined and $w=\sup_aT_aw$ satisfies $w\ge v^*$.
--
--   As the proof on p. 886 says, a competing solution is not assumed absolutely measurable, only that the integrals $T_aw(s)$ are defined. The negative case of this theorem is the published item `NegativeDP.OptEq.theorem82`; together with this item it covers the whole source theorem.
--
--   **Formalization Note** $T_av^*$ is a Bochner integral of the bounded, absolutely measurable (Theorem 7.1) function $r+\beta v^*$; no measurability of $v^*$ is assumed. "$T_aw(s)$ is defined" is read as measurability of the actual integrand $r(s,a,\cdot)+\beta w$ for the completion of each $q(\cdot\mid s,a)$ in D (`AEStronglyMeasurable`); boundedness then gives integrability. At $\beta=0$ this imposes no measurability condition on $w$. In P, `AEMeasurable w` is equivalent to completion measurability of the non-negative integrand $r(s,a,\cdot)+w$. In case P the comparison equation is written with lower Lebesgue integrals in $[0,\infty]$, so an unbounded non-negative $w$ is allowed and no integrability is presupposed.
--
--   Differences from the source:
--   - encoding: one theorem for the cases D, P, N → the cases not yet published (D and P); the negative case is the published NegativeDP.OptEq.theorem82; reason: the negative case is already published and immutable; the two items together state the whole theorem
--   - reading: w is a solution for which Tₐw is defined for each a (proof, p. 886) → completion-measurable r(s,a,·) + βw in D (AEStronglyMeasurable); completion-measurable w in P (AEMeasurable); reason: these are the actual integrands being integrated; boundedness gives D integrability, nonnegativity gives a defined P integral, and β=0 places no condition on w
--   - encoding: P: w ≥ 0 with w = supₐ Tₐw → real w ≥ 0 with ofReal (w s) = ⨆ a, ∫⁻ ofReal (r + w) dq(· | s, a); reason: for r, w ≥ 0 the lower Lebesgue integral is the integral Tₐw(s), with value +∞ when it diverges
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966) 871–890, DOI 10.1214/aoms/1177699369, p. 885, Theorem 8.2

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Supplement_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan Problem I T Ta U optReturn IsOptimal IsBM supNorm stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.EssFinite.Supplement

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 8.2 (pp. 885–886), discounted case (first conjunct) and positive bounded case
(second conjunct): `v*(s) = supₐ Tₐv*(s)` for all `s`; in the discounted case `v*` is the unique
bounded solution, and in the positive bounded case `v*` is the smallest non-negative solution.
Competing solutions `w` are only required to have every integral `Tₐw(s)` defined (as the proof
on p. 886 says), not to be Borel. In case D measurability is required of the actual integrand,
so at `β = 0` no measurability of `w` is required. In case P the comparison `Tₐw` of a non-negative `w` is a
lower Lebesgue integral in `[0, ∞]`. The negative case is the published
`NegativeDP.OptEq.theorem82`. -/
theorem theorem82 :
    (∀ P : Problem S A,
      (∀ s, optReturn P s = ⨆ a : A, Ta P a (optReturn P) s) ∧
      ∀ w : S → ℝ, (∃ C : ℝ, ∀ s, |w s| ≤ C) →
        (∀ s a, AEStronglyMeasurable (fun t => P.r (s, a, t) + P.β * w t) (P.q (s, a))) →
        (∀ s, w s = ⨆ a : A, Ta P a w s) → w = optReturn P) ∧
    (∀ P : Pos.Problem S A,
      (∀ s, Pos.optReturn P s = ⨆ a : A, Pos.Ta P a (Pos.optReturn P) s) ∧
      ∀ w : S → ℝ, (∀ s, 0 ≤ w s) → (∀ s a, AEMeasurable w (P.q (s, a))) →
        (∀ s, ENNReal.ofReal (w s) =
          ⨆ a : A, ∫⁻ t, ENNReal.ofReal (P.r (s, a, t) + w t) ∂P.q (s, a)) →
        ∀ s, Pos.optReturn P s ≤ w s) := by sorry

end NegativeDP.EssFinite.Supplement
