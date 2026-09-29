-- Prove2me | Theorems.Thm_ModularCurve_UniformizedHeckeCurve_exists_transport_of_algEquiv
-- name    : ModularCurve.UniformizedHeckeCurve.exists_transport_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/588a4123-5d43-5041-91f9-2dca982924d7
-- title:
--   Transport of a uniformised Hecke curve along a ℂ-algebra isomorphism
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$, let $F_c$ and $F_c'$ be fields with $\mathbb{C}$-algebra structures, let $e : F_c \xrightarrow{\sim} F_c'$ be an isomorphism of $\mathbb{C}$-algebras, and let $U$ be a uniformised Hecke curve structure for $\Gamma$ on $F_c$: a family of places $\mathrm{pt}(\tau)$ of $F_c$ over $\mathbb{C}$ (proper valuation subrings containing $\mathbb{C}$ that are principal ideal rings) indexed by $\tau$ in the upper half-plane, a realisation map $\mathrm{realize} : F_c \to \mathcal{H} \to \mathbb{C}$, positive ramification indices, together with the axioms that $x$ lies in the valuation ring at $\tau$ exactly when $\|\mathrm{realize}\,x\|$ is bounded near $\tau$ on punctured neighbourhoods, that the meromorphic order of $\mathrm{realize}\,x$ at $\tau$ is the ramification index times $\mathrm{ord}_{\mathrm{pt}(\tau)}(x)$ for $x \neq 0$, that $\mathrm{pt}(\tau) = \mathrm{pt}(\tau')$ iff $\tau' \in \Gamma\tau$, that twice the ramification index is the order of the stabiliser of $\tau$ in $\Gamma$, a distinguished element of $F_c$ whose valuation ring membership forces a place to be of the form $\mathrm{pt}(\tau)$, and, for each prime $\ell$, a multiset $\mathrm{heckePoints}(\ell)$ in $\mathrm{GL}_2(\mathbb{R})$ and an endomorphism $\mathrm{corr}(\ell)$ of the divisor group $\mathrm{Place}\,\mathbb{C}\,F_c \to_{0} \mathbb{Z}$ sending $\mathrm{pt}(\tau)$ to $\sum_{\delta} \mathrm{pt}(\delta\tau)$. Write $pm$ for the bijection on places induced by restriction along $e^{-1} : F_c' \to F_c$ (an integral, indeed surjective, map), namely pulling back a valuation subring of $F_c$ along $e^{-1}$. Then there is a uniformised Hecke curve structure $U'$ for $\Gamma$ on $F_c'$ with $U'.\mathrm{pt}(\tau) = pm(U.\mathrm{pt}(\tau))$, $U'.\mathrm{realize}\,x\,\tau = U.\mathrm{realize}\,(e^{-1}x)\,\tau$, the same ramification indices and the same Hecke point multisets, distinguished element $e(U.\mathrm{distinguished})$, and $U'.\mathrm{corr}(\ell)$ compatible with $U.\mathrm{corr}(\ell)$ under the pushforward of divisors along $pm$.
--
--   This is the transport-of-structure statement for uniformised Hecke curves: the whole package of uniformisation data, Hecke points and Hecke correspondences moves along any isomorphism of the underlying function field over $\mathbb{C}$. It is used to import the quaternionic uniformisation onto the function field of the relevant coarse moduli curve, in [`CerednikDrinfeld.QM.exists_uniformizedHeckeCurve_bcPlace_corr_single_eq_sum_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.exists_uniformizedHeckeCurve_bcPlace_corr_single_eq_sum_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UniformizedHeckeCurve_exists_transport_of_algEquiv.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology

theorem ModularCurve.UniformizedHeckeCurve.exists_transport_of_algEquiv
    (Γ : Subgroup (GL (Fin 2) ℝ)) {Fc Fc' : Type} [Field Fc] [Algebra ℂ Fc] [Field Fc'] [Algebra ℂ Fc']
    (e : Fc ≃ₐ[ℂ] Fc') (U : ModularCurve.UniformizedHeckeCurve Γ Fc) :
    let pm : Place ℂ Fc → Place ℂ Fc' := fun P =>
      P.restrictAlong (e.symm : Fc' →ₐ[ℂ] Fc) ((e.symm : Fc' →ₐ[ℂ] Fc).toRingHom.isIntegral_of_surjective e.symm.surjective)
    ∃ U' : ModularCurve.UniformizedHeckeCurve Γ Fc',
      (∀ τ : UpperHalfPlane, U'.pt τ = pm (U.pt τ)) ∧
      (∀ (x : Fc') (τ : UpperHalfPlane), U'.realize x τ = U.realize (e.symm x) τ) ∧
      (∀ τ : UpperHalfPlane, U'.ramification τ = U.ramification τ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), U'.heckePoints ℓ hℓ = U.heckePoints ℓ hℓ) ∧
      U'.distinguished = e U.distinguished ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (D : Divisor ℂ Fc),
        U'.corr ℓ hℓ (Finsupp.mapDomain pm D) = Finsupp.mapDomain pm (U.corr ℓ hℓ D)) := by sorry
