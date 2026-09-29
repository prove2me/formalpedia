-- Prove2me | Theorems.Thm_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius
-- name    : HopfAlgebra.natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/2f76ee0a-b02d-5d4b-8467-168c8796297e
-- title:
--   Point counts of G and G^∨ multiply to dim B
-- statement:
--   Let $q$ be a prime, so that $\mathbb{Z}/q$ is the field with $q$ elements, and let $B$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}/q$ which is finite as a $\mathbb{Z}/q$-module and whose comultiplication is cocommutative. Assume there is an $N \in \mathbb{N}$ such that the identity map of $B$, viewed as an element of the convolution monoid on $\operatorname{Hom}_{\mathbb{Z}/q}(B,B)$, satisfies $\mathrm{id}^{q^N} = 1$, the convolution unit (so the group scheme $\operatorname{Spec} B$ is killed by $q^N$). Let $T : B \to B$ be a bijective bialgebra endomorphism, let $Fk : B \to B$ be a bialgebra endomorphism with $Fk(x) = x^q$ for all $x$, and let $FD$ be an algebra endomorphism of the Cartier dual $\mathrm{CartierDual}(\mathbb{Z}/q, B)$, that is of the $\mathbb{Z}/q$-linear dual of $B$ with its dual Hopf structure, with $FD(\psi) = \psi^q$ for all $\psi$. Assume finally that the linear map underlying the transpose $\mathrm{CartierDual.map}\,T$ of $T$ is the convolution product of the linear map underlying $\mathrm{CartierDual.map}\,Fk$ with that underlying $FD$. Then the number of $\mathbb{Z}/q$-algebra homomorphisms from $B$ to an algebraic closure of $\mathbb{Z}/q$, times the number of such homomorphisms from the Cartier dual of $B$, equals $\dim_{\mathbb{Z}/q} B$.
--
--   For a finite commutative $q$-primary group scheme $G = \operatorname{Spec} B$ over $\mathbb{F}_q$ whose given automorphism is the sum of the Frobenius of $G$ and its Verschiebung, this says that the geometric point counts of $G$ and of its Cartier dual $G^\vee$ multiply to the order of $G$; it rests on the connected–étale sequence and Cartier duality. It is used in the two lemmas on the action of inertia on torsion of modular Jacobians, [`ModularCurve.inertia_smul_eq_nsmul_of_forall_exists_heckeOperatorBar_pow_apply_eq_of_reductionModL_eq_zero`](thm.html#ModularCurve.inertia_smul_eq_nsmul_of_forall_exists_heckeOperatorBar_pow_apply_eq_of_reductionModL_eq_zero) and its variant `…_of_ne_two`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius.lean

import Definitions.Def_HopfAlgebra_CartierDualMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.natCard_algHom_mul_natCard_algHom_cartierDual_eq_finrank_of_map_eq_conv_frobenius
    (q : ℕ) [Fact q.Prime] (B : Type) [CommRing B] [HopfAlgebra (ZMod q) B]
    [Module.Finite (ZMod q) B] [Coalgebra.IsCocomm (ZMod q) B]
    (N : ℕ) (hN : WithConv.toConv (LinearMap.id : B →ₗ[ZMod q] B) ^ (q ^ N) = 1)
    (T : B →ₐc[ZMod q] B) (hT : Function.Bijective T)
    (Fk : B →ₐc[ZMod q] B) (hFk : ∀ x, Fk x = x ^ q)
    (FD : CartierDual (ZMod q) B →ₐ[ZMod q] CartierDual (ZMod q) B) (hFD : ∀ ψ, FD ψ = ψ ^ q)
    (hFV : (CartierDual.map T : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) =
      (WithConv.toConv
          (CartierDual.map Fk : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B) *
        WithConv.toConv
          (FD : CartierDual (ZMod q) B →ₗ[ZMod q] CartierDual (ZMod q) B)).ofConv) :
    Nat.card (B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) *
        Nat.card (CartierDual (ZMod q) B →ₐ[ZMod q] AlgebraicClosure (ZMod q)) =
      Module.finrank (ZMod q) B := by sorry
