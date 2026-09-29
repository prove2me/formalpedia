-- Prove2me | Theorems.Thm_ModularCurve_HpoolLevelRing_exists_pFibre_dictionary
-- name    : ModularCurve.HpoolLevelRing.exists_pFibre_dictionary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/e8eecc24-1135-517e-878e-4e5b96023772
-- title:
--   Characteristic-p fibre dictionary for the modular unit
-- statement:
--   Let $p$ be a prime with $5 \le p$, and let $F =$ `modularFunctionFieldFull p` be the subfield of the Laurent series field over $\mathbb Q$ generated over $\mathbb Q$ by the $q$-expansions $j(q^d)$ for the positive divisors $d$ of $p$. Assume the Laurent series $u =$ `modularUnitSeries p`, the quotient of the $\Delta$-expansion by its substitution $q \mapsto q^{p}$, lies in $F$. Let $A =$ `HpoolLevelRing.Afin p` be the finite chart $\mathbb Z$-subalgebra `chartAlgFin` of $F$ attached to the element `IgusaScheme.jFull p` of $F$, and let $v \in A$ be an element whose image in $F$ is either $u$ or $p^{12}u^{-1}$. Then there are prime ideals $P_u \ne P_z$ of $A$ such that the minimal primes of the ideal $pA$ are exactly $P_u$ and $P_z$, such that $P_u \cap P_z = pA$, and such that $v \notin P_u$ while $v \in P_z$; moreover there is a ring isomorphism $e : A/P_u \xrightarrow{\sim} \mathbb F_p[X]$ and a polynomial $U \in \mathbb F_p[X]$ with $e(v \bmod P_u) = U$, with $U$ of degree $p-1$, and with derivative $U' \ne 0$.
--
--   This is the ring-theoretic description of the characteristic-$p$ fibre of the finite-$j$ chart of the integral model of $X_0(p)$, recording that this fibre has exactly two components meeting in the reduced ideal $pA$, that the modular unit $\Delta(q)/\Delta(q^p)$ (or its Fricke partner $p^{12}u^{-1}$) vanishes on one of them and not on the other, and that on the non-vanishing component it becomes a polynomial of degree $p-1$ with nonzero derivative in an affine coordinate. It feeds the analysis of stalks along the crossing of the two components and the construction of a finite étale extension of the level ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_HpoolLevelRing_exists_pFibre_dictionary.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.HpoolLevelRing.exists_pFibre_dictionary
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p) (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p)
    (v : HpoolLevelRing.Afin p)
    (hv : (v : ↥(ModularCurve.modularFunctionFieldFull p)) = ⟨modularUnitSeries p, hmem⟩ ∨
      (v : ↥(ModularCurve.modularFunctionFieldFull p)) = (p : ↥(ModularCurve.modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull p))⁻¹) :
    ∃ (Pu Pz : Ideal (HpoolLevelRing.Afin p)),
      Pu.IsPrime ∧ Pz.IsPrime ∧ Pu ≠ Pz ∧
      (Ideal.span {(p : HpoolLevelRing.Afin p)}).minimalPrimes = {Pu, Pz} ∧
      Pu ⊓ Pz = Ideal.span {(p : HpoolLevelRing.Afin p)} ∧
      v ∉ Pu ∧ v ∈ Pz ∧
      ∃ (e : (HpoolLevelRing.Afin p ⧸ Pu) ≃+* Polynomial (ZMod p)) (U : Polynomial (ZMod p)),
        e (Ideal.Quotient.mk Pu v) = U ∧ U.natDegree = p - 1 ∧ Polynomial.derivative U ≠ 0 := by sorry
