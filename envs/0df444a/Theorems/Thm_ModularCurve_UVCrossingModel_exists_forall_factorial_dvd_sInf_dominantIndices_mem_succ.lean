-- Prove2me | Theorems.Thm_ModularCurve_UVCrossingModel_exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ
-- name    : ModularCurve.UVCrossingModel.exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/054d28b2-dc8a-53d6-88ae-09b158af00b4
-- title:
--   A factorial scale at which dominant indices persist
-- statement:
--   Let $W$ be a commutative ring, let $v : W \to \mathbb{N}\cup\{\infty\}$ be any function with $v(0)=\infty$, and let $E$ be a natural number with $1 \le E$. Let $ab=(a,b)$ be a pair of one-variable power series over $W$ whose second component has vanishing constant coefficient, and assume that some index $n \in \mathbb{Z}$ has $v(\mathrm{nfCoeff}\,ab\,n) \neq \infty$, where $\mathrm{nfCoeff}\,ab$ reads off the coefficient of $U^{i}$ in $a$ at $n = i \ge 0$ and the coefficient of $V^{j+1}$ in $b$ at $n = -(j+1)$. Here, for an order function $v$, weight exponent $E$ and depth $t$, $\mathrm{dominantIndices}\,v\,E\,t\,ab$ is the set of $n \in \mathbb{Z}$ whose term order $v(\mathrm{nfCoeff}\,ab\,n) + \mathrm{annulusWeight}\,E\,t\,(\mathrm{nfExponent}\,n)$ attains $\mathrm{repGaussOrder}\,v\,E\,t$ of the element $\mathrm{inU}\,a + \mathrm{inV}\,b$, that is the infimum over multi-degrees $d$ of $v(\mathrm{coeff}_d) + \mathrm{annulusWeight}\,E\,t\,d$. The assertion is that there exists $N \in \mathbb{N}$ such that for every $r \ge 1$ divisible by $N!$, and with the order function $r\cdot v$ and weight exponent $rE$: for each $S$ with $S+1 \le rE$, the infimum of $\mathrm{dominantIndices}$ at depth $S$ lies in $\mathrm{dominantIndices}$ at depth $S+1$; and for each $S$ with $1 \le S \le rE$, the supremum at depth $S$ lies in $\mathrm{dominantIndices}$ at depth $S-1$. The infimum and supremum are those of the conditionally complete order on $\mathbb{Z}$.
--
--   This is the factorial-refinement statement for the Gauss-order polygon of a normal form on the crossing model: after rescaling the order function and the weight exponent by a suitable $r$, the extreme dominant index at each integral depth remains dominant at the neighbouring depth, so that no corner of the polygon falls strictly between consecutive grid depths. It is used by [`ModularCurve.UVCrossingModel.sInf_dominantIndices_mul_and_sSup_dominantIndices_mul`](thm.html#ModularCurve.UVCrossingModel.sInf_dominantIndices_mul_and_sSup_dominantIndices_mul), [`ModularCurve.UVCrossingModel.sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul`](thm.html#ModularCurve.UVCrossingModel.sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul) and, through them, by [`ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_circleIndexDrop`](thm.html#ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_circleIndexDrop).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UVCrossingModel_exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ.lean

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ
    {W : Type u} [CommRing W] (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E : ℕ) (hE : 1 ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤) :
    ∃ N : ℕ, ∀ r : ℕ, 1 ≤ r → Nat.factorial N ∣ r →
      (∀ S : ℕ, S + 1 ≤ r * E →
        sInf (dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) S ab) ∈
          dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) (S + 1) ab) ∧
      (∀ S : ℕ, 1 ≤ S → S ≤ r * E →
        sSup (dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) S ab) ∈
          dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) (S - 1) ab) := by sorry
