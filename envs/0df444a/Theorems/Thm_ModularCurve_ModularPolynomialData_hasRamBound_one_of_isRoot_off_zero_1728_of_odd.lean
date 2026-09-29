-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_hasRamBound_one_of_isRoot_off_zero_1728_of_odd
-- name    : ModularCurve.ModularPolynomialData.hasRamBound_one_of_isRoot_off_zero_1728_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/14a940b6-1538-5292-8f70-96d58698c43a
-- title:
--   Roots of Φ_N(a+t,Y) are Laurent series for odd N
-- statement:
--   Let $N$ be a nonzero natural number which is odd, and let `data` be a modular polynomial datum of level $N$: a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ that is monic, whose degree in $Y$ equals $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ (the Dedekind $\psi(N)$), and which satisfies $\Phi(j, j_N) = 0$, the coefficients in $\mathbb{Z}[X]$ being evaluated at the $q$-expansion $j$ inside the Laurent series field over $\mathbb{Q}$ and $Y$ at the expansion of $j$ at $q^N$. Let $a$ be an element of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with $a \neq 0$ and $a \neq 1728$, and let $r$ be a Hahn series with rational exponents and coefficients in $\overline{\mathbb{Q}}$. Assume $r$ is a root of the one-variable polynomial obtained from $\Phi$ by applying to each coefficient in $\mathbb{Z}[X]$ the ring homomorphism that maps $\mathbb{Z}$ into the Hahn series field and sends $X$ to $a + t$, where $t$ denotes the Hahn series `HahnSeries.single 1 1`. Then $r$ has ramification bound $1$, i.e. the support of $r$ is contained in the set of rationals of the form $k/1$ with $k \in \mathbb{Z}$; equivalently, $r$ is an honest Laurent series in $t$.
--
--   This is the statement that the covering $X_0(N) \to X(1)$ is unramified over every $j$-value $a \notin \{0, 1728, \infty\}$, for odd level $N$, expressed through the branches of $\Phi_N(a+t, Y) = 0$ in the field of Hahn series with rational exponents. It feeds the computation of the order of vanishing of $\bar{j} - a$ along such a fibre in [`ModularCurve.ord_jBar_sub_eq_one_of_ne_zero_of_ne_of_odd`](thm.html#ModularCurve.ord_jBar_sub_eq_one_of_ne_zero_of_ne_of_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_hasRamBound_one_of_isRoot_off_zero_1728_of_odd.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ModularPolynomialData.hasRamBound_one_of_isRoot_off_zero_1728_of_odd
    {N : ℕ} [NeZero N] (hN : Odd N) (data : ModularCurve.ModularPolynomialData N)
    (a : AlgebraicClosure ℚ) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728)
    (r : HahnSeries ℚ (AlgebraicClosure ℚ))
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
      (HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r) :
    HahnSeries.HasRamBound 1 r := by sorry
