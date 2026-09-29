-- Prove2me | Theorems.Thm_ModularCurve_natCard_torsion_jOneC_eq_natCard_regularDifferentials_x1FunctionFieldC_coeff_mul_eq_pow
-- name    : ModularCurve.natCard_torsion_jOneC_eq_natCard_regularDifferentials_x1FunctionFieldC_coeff_mul_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/15660856-cb1a-5ffc-b506-e426c888d6dd
-- title:
--   p-torsion of J₁(M) counted by Cartier-fixed differentials
-- statement:
--   Let $k$ be an algebraically closed field of characteristic a prime $p$, let $M \ge 1$ and assume $p \nmid M$. Let $F_1 =$ [`ModularCurve.x1FunctionFieldC k M`](def/ModularCurve_X1.html#L134) be the intermediate field of $k((q))$ obtained by adjoining to $k$ the set of ratios of integral $q$-expansions attached to $\Gamma_1(M)$, and let $\mathrm{JOneC}$ be $\mathrm{Pic}^0$ of $F_1$ over $k$, i.e. the group of degree-zero divisors modulo principal divisors, the divisors being supported on the places of $F_1/k$ in the sense of the project's `Place` structure (valuation subrings of $F_1$ containing the image of $k$, not equal to $F_1$, whose valuation ring is a principal ideal ring). The assertion is an equality of cardinalities: the number of $y \in \mathrm{Pic}^0(F_1/k)$ with $p \cdot y = 0$ equals the number of elements $\omega$ of the $k$-submodule of regular differentials in $\Omega_{F_1/k}$ — those $\omega$ such that for every place $v$ there is $f$ in the valuation subring of $v$ with $\omega = f \cdot \mathrm{d}\pi_v$, $\pi_v$ a uniformiser of $v$ — which satisfy, writing $\varphi$ for the $k$-linear map $\Omega_{F_1/k} \to k((q))$ determined by $\varphi(\mathrm{d}x) = \theta(x)$ and $\varphi(f \cdot \omega) = f \, \varphi(\omega)$ along the inclusion $F_1 \subseteq k((q))$ (with $\theta = q\,\mathrm{d}/\mathrm{d}q$), the coefficient conditions $\varphi(\omega)_{np} = (\varphi(\omega)_n)^p$ for all $n \in \mathbb{Z}$.
--
--   This is Serre's description of the $p$-torsion of the Jacobian of a curve in characteristic $p$, specialised to the $q$-expansion model of $X_1(M)$ for $p \nmid M$: the $p$-torsion classes correspond bijectively to the regular differentials fixed by the Cartier operator, which on $q$-expansions is the condition $a_{np} = a_n^p$. It feeds the subsequent bound on $\#J_1(M)(k)[p]$ in terms of the characteristic polynomial of the Hecke operator considered there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_torsion_jOneC_eq_natCard_regularDifferentials_x1FunctionFieldC_coeff_mul_eq_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.natCard_torsion_jOneC_eq_natCard_regularDifferentials_x1FunctionFieldC_coeff_mul_eq_pow
    (k : Type*) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) :
    Nat.card {y : ModularCurve.JOneC M k // p • y = 0} =
      Nat.card {ω : ↥(AlgebraicCurve.regularDifferentials k ↥(ModularCurve.x1FunctionFieldC k M)) //
        ∀ n : ℤ, (ModularCurve.qExpansionDiffAlong (ModularCurve.x1FunctionFieldC k M).val
            (ω : Ω[↥(ModularCurve.x1FunctionFieldC k M)⁄k])).coeff (n * p) =
          (ModularCurve.qExpansionDiffAlong (ModularCurve.x1FunctionFieldC k M).val
            (ω : Ω[↥(ModularCurve.x1FunctionFieldC k M)⁄k])).coeff n ^ p} := by sorry
