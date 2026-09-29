-- Prove2me | Theorems.Thm_MvFormalGroup_Hom_eq_of_forall_subst_curve_eq
-- name    : MvFormalGroup.Hom.eq_of_forall_subst_curve_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/aeb460de-5031-5ae4-b17a-93cd28cd2bae
-- title:
--   Homomorphisms of formal group laws are determined on curves
-- statement:
--   Let $R$ be a commutative ring and let $d,d'$ be natural numbers. Let $\Phi$ be a $d$-dimensional formal group law over $R$, that is, a family of $d$ power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ whose constant coefficients vanish, whose coefficients at the degree-one monomials in each of the two blocks are $\delta_{ij}$, and which satisfies the associativity identity under substitution; let $\Phi'$ be such a law of dimension $d'$. Let $\varphi,\psi$ be homomorphisms $\Phi \to \Phi'$, each given by $d'$ power series in the $\mathrm{Fin}\,d$ variables with vanishing constant coefficients such that substituting the law $\Phi$ into the $i$-th component equals substituting the two blockwise copies of the components into the $i$-th component of $\Phi'$. Assume that for every family $\gamma : \mathrm{Fin}\,d \to R[[t]]$ of one-variable power series with $\gamma_j(0)=0$ for all $j$, and every index $k$ in $\mathrm{Fin}\,d'$, one has $\mathrm{subst}\,\gamma\,(\varphi_k) = \mathrm{subst}\,\gamma\,(\psi_k)$. Then $\varphi = \psi$ as elements of `Φ.Hom Φ'`.
--
--   This is the faithfulness of the passage from a homomorphism of formal group laws to its induced map on curves: two homomorphisms agreeing on all curves $\gamma \in tR[[t]]^d$ coincide. It is used in the Cartier-module layer, in [`MvFormalGroup.CartierModule.eq_of_forall_map_eq_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.eq_of_forall_map_eq_of_algebra_padicInt), to recognise equality of homomorphisms from equality of the induced maps of curve modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_Hom_eq_of_forall_subst_curve_eq.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.Hom.eq_of_forall_subst_curve_eq
    {R : Type u} [CommRing R] {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R)
    (φ ψ : Φ.Hom Φ')
    (h : ∀ γ : Fin d → PowerSeries R, (∀ j, PowerSeries.constantCoeff (γ j) = 0) →
      ∀ k, MvPowerSeries.subst γ (φ.toPowerSeries k) = MvPowerSeries.subst γ (ψ.toPowerSeries k)) :
    φ = ψ := by sorry
