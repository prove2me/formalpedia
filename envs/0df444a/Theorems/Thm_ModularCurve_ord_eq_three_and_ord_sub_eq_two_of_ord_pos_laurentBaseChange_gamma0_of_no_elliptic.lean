-- Prove2me | Theorems.Thm_ModularCurve_ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic
-- name    : ModularCurve.ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/7a9adc76-7f47-5e9c-b5c8-3c9762a7100e
-- title:
--   No elliptic points: ord_P j=3, ord_P(j-1728)=2 on X₀(N)
-- statement:
--   Let $K$ be an algebraically closed field equipped with a $\mathbb{Q}$-algebra structure, and let $N\ge 1$. Write $F_K$ for `laurentBaseChange K (qExpFunctionFieldC ℚ (Gamma0 N))`, the intermediate field of $K((q))$ generated over $K$ by the coefficientwise image of `qExpFunctionFieldC ℚ (Gamma0 N)`, the latter being the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients of integral $q$-expansions of pairs of modular forms of equal weight for $\Gamma_0(N)$. Let $y\in F_K$ be an element whose underlying Laurent series is `jqModC K`, that is $q^{-1}\cdot E_4^3\eta^{-24}$, the $q$-expansion of the modular invariant $j$. Places here are valuation subrings of $F_K$ containing $K$, distinct from $F_K$ and principal ideal rings, and $\operatorname{ord}_P$ is minus the logarithm of the associated adic valuation. The assertion is the conjunction of two implications: if $9\mid N$ or some prime $\ell\equiv 2\pmod 3$ divides $N$, then every place $P$ with $\operatorname{ord}_P(y)>0$ has $\operatorname{ord}_P(y)=3$; and if $4\mid N$ or some prime $\ell\equiv 3\pmod 4$ divides $N$, then every place $P$ with $\operatorname{ord}_P(y-1728)>0$ has $\operatorname{ord}_P(y-1728)=2$.
--
--   The two numerical hypotheses are exactly the conditions $\nu_3(N)=0$ and $\nu_2(N)=0$ that $\Gamma_0(N)$ have no elliptic points of order $3$, respectively $2$; under them the covering $X_0(N)\to X(1)$ is totally ramified of degree $3$ above $j=0$ and of degree $2$ above $j=1728$, in the form of orders of vanishing of $j$ and $j-1728$ at the places of the function field. It feeds the computation of ramification indices along the map $X_1(N)\to X_0(N)$ in the tame case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CongruenceSubgroup AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (N : ℕ) [NeZero N]
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))))
    (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :

    ((9 ∣ N ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ N ∧ ℓ % 3 = 2) →
      ∀ P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))),
        0 < P.ord y → P.ord y = 3) ∧

    ((4 ∣ N ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ N ∧ ℓ % 4 = 3) →
      ∀ P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))),
        0 < P.ord (y - 1728) → P.ord (y - 1728) = 2) := by sorry
