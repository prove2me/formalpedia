-- Prove2me | Theorems.Thm_ModularCurve_exists_iterate_diamond_eq_self_pic0_fbar
-- name    : ModularCurve.exists_iterate_diamond_eq_self_pic0_fbar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/c7892636-b84c-5d61-82a8-d3d96b0f3990
-- title:
--   Finite order of a diamond operator on Pic⁰ mod p
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$, and let $\kappa$ be an algebraically closed field of characteristic $p$. Write $F =$ `Fbar p M H hpM κ` for the $q$-expansion function field over $\kappa$ at level `ΓN p M H hpM`, and let $\mathrm{Pic}^0_\kappa(F)$ be its degree-zero divisor class group, that is, the quotient of the group of degree-zero divisors (finitely supported $\mathbb{Z}$-valued functions on the places of $F$ over $\kappa$) by the subgroup of principal divisors. Let $pb \in (\mathbb{Z}/(M/p))^\times$ and let $H'$ = `infSubgroup p M H hpM` be the image of $H$ in $(\mathbb{Z}/(M/p))^\times$ under the reduction map on units. Suppose $\delta$ is an additive endomorphism of $\mathrm{Pic}^0_\kappa(F)$ which, on every class $z$, agrees with the action of the semilinear automorphism $(\sigma, \mathrm{id}_\kappa)$ attached to $\sigma =$ `diamondActionModL κ (M/p) H'` evaluated at [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36), a chosen element of $\Gamma_0(M/p)$ whose associated unit is $pb$; here `diamondActionModL` is a chosen homomorphism $\Gamma_0(M/p) \to \mathrm{Aut}_\kappa$ of the level-$H'$ function field satisfying the diamond pull-back condition when one exists, and the trivial homomorphism otherwise. Then there is $m > 0$ such that the $m$-fold iterate of $\delta$ fixes every element of $\mathrm{Pic}^0_\kappa(F)$.
--
--   This is the statement that a diamond operator $\langle pb \rangle$ acts with finite order on the degree-zero divisor class group of the reduction of the level-$H'$ modular curve in characteristic $p$, reflecting the classical fact that $\langle d \rangle$ depends only on $d$ modulo the level and is trivial on $\Gamma_1$. It is used in the analysis of fixed classes of diamond-twisted Frobenius, in [`ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self`](thm.html#ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self) and [`ModularCurve.finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self`](thm.html#ModularCurve.finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_iterate_diamond_eq_self_pic0_fbar.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

theorem ModularCurve.exists_iterate_diamond_eq_self_pic0_fbar
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (pb : (ZMod (M / p))ˣ)
    (δ : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL κ (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z) :
    ∃ m : ℕ, 0 < m ∧ ∀ z, (⇑δ)^[m] z = z := by sorry
