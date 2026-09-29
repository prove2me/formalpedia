-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv
-- name    : ModularCurve.FullLevel.AuxLevel.forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/5ae284db-fe5c-5bd3-95e4-9381257d5985
-- title:
--   Translation level automorphism preserves maximal-ideal q-expansion coefficients
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\neq q$, and let $M'\ge 1$ satisfy $q\nmid M'$ and $\ell\nmid M'$. Let $L$ be a field of characteristic $0$, $\xi\in L$ a primitive $(q\ell)$-th root of unity, and assume there is a ring homomorphism $\iota_0:L\to\mathbb C$ with $\iota_0(\xi)=e^{2\pi i/(q\ell)}$. Let $K$ be the intermediate field of $L\subseteq L((T))$ obtained as `laurentBaseChange`, namely the subfield generated over $L$ by the coefficientwise image of the field `xHFunctionField` of $q$-expansions of modular functions for $\Gamma_H$ at level $N_0=(q\ell)^2M'$ with $H=\ker\bigl((\mathbb Z/(q\ell)^2M')^\times\to(\mathbb Z/q\ell)^\times\bigr)$. Let $A$ be a Henselian discrete valuation ring with fraction field $L$, algebraically closed residue field, $q\in\mathfrak m_A$ and $\xi$ in the image of $A$, with $K$ an $A$-algebra compatibly with $A\to L\to K$. Let $s\in\mathbb Z$ with $q\mid s$ and let $\tau$ be an $L$-automorphism of $K$ satisfying `IsLevelAutAt` for the element $(T^{s})^{-1}$ of $\mathrm{SL}_2(\mathbb Z)$, with parameters $n=m=q\ell$, $\zeta=\xi$, $N_0$, $H$: for every weight $k$, every pair of weight-$k$ modular forms $f,g$ for $\Gamma_H(N_0)$ with integral $q$-expansions given by power series $p_f,p_g$ over $\mathbb Z$, with $p_g$ having nonzero Laurent series over $\mathbb Q$, every $x\in K$ whose Laurent series is the coefficientwise image in $L((T))$ of $p_f/p_g$, and every $\iota:L\to\mathbb C$ with $\iota(\xi)=e^{2\pi i/(q\ell)}$, one has $\iota_*(\tau x)\cdot (g\mid_k \mathrm{diag}(q\ell,1)^{-1}T^{-s}\mathrm{diag}(q\ell,1))^{\wedge}=(f\mid_k \mathrm{diag}(q\ell,1)^{-1}T^{-s}\mathrm{diag}(q\ell,1))^{\wedge}$ as $q$-expansions of width $1$. Then for every $a\in K$: all Laurent coefficients of $a$ lie in the image of $\mathfrak m_A$ under $A\to L$ if and only if all Laurent coefficients of $\tau a$ do.
--
--   The automorphism attached to the translation $z\mapsto z-s/(q\ell)$ multiplies the $n$-th $q$-expansion coefficient by a root of unity lying in $A^\times$, so it preserves the condition that all coefficients lie in $\mathfrak m_A$; this is the invariance, under the unipotent part of the level group, of the prime of the $j$-finite chart algebra cut out by the cusp $\infty$. It feeds into [`ModularCurve.FullLevel.AuxLevel.forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_gamma_of_drinfeldChartWitness`](thm.html#ModularCurve.FullLevel.AuxLevel.forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_gamma_of_drinfeldChartWitness), where the same invariance is established for general elements of the level group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.forall_coeff_mem_maximalIdeal_iff_of_isLevelAutAt_T_zpow_inv
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (s : ℤ) (hs : (q : ℤ) ∣ s)
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') (ModularGroup.T ^ s)⁻¹ K τ)
    (a : ↥K) :
    (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ↔
    (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((τ a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) := by sorry
