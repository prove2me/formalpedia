-- Prove2me | Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing
-- name    : HopfAlgebra.exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/26cd7ace-6d4b-5906-ace3-5a8e422426eb
-- title:
--   Maximal multiplicative-type quotient of a finite flat Hopf algebra
-- statement:
--   Let $R$ be a commutative ring which is a henselian local ring, and let $H$ be a commutative ring carrying a Hopf algebra structure over $R$ whose coalgebra structure is cocommutative, and which is finite and flat as an $R$-module. Then there exists a type $M$ (in the same universe as $H$) equipped with a commutative ring structure, a Hopf algebra structure over $R$, a cocommutative coalgebra structure, and free and finite $R$-module structures, together with a bialgebra homomorphism $\pi \colon H \to M$ over $R$, such that: (i) $\pi$ is surjective; (ii) [`CartierDual R M`](def/HopfAlgebra_CartierDual.html#L12), i.e. the $R$-linear dual $\operatorname{Hom}_R(M,R)$ with its algebra structure, is étale over $R$; (iii) for every $M'$ that is a commutative ring with a cocommutative Hopf algebra structure over $R$, finite and free as an $R$-module, and with $\operatorname{Hom}_R(M',R)$ étale over $R$, and every bialgebra homomorphism $f \colon H \to M'$ over $R$, there is a unique bialgebra homomorphism $g \colon M \to M'$ with $f = g \circ \pi$; (iv) for every bialgebra endomorphism $\varphi$ of $H$ there is a unique bialgebra endomorphism $\psi$ of $M$ with $\psi \circ \pi = \pi \circ \varphi$; and (v) for every commutative ring $R'$ (in the universe of $R$) which is henselian local and an $R$-algebra whose structure map is a local homomorphism, the dual $\operatorname{Hom}_{R'}(R' \otimes_R M, R')$ is étale over $R'$, and for every $N$ that is a commutative ring with a cocommutative Hopf algebra structure over $R'$, finite and free over $R'$ and with $\operatorname{Hom}_{R'}(N,R')$ étale over $R'$, and every $R'$-bialgebra homomorphism $f \colon R' \otimes_R H \to N$, there is a unique $R'$-bialgebra homomorphism $g \colon R' \otimes_R M \to N$ whose composite with the base change $\mathrm{id}_{R'} \otimes \pi$ equals $f$.
--
--   In the language of group schemes, with $G = \operatorname{Spec} H$ a finite flat commutative group scheme over a henselian local base, this is the existence of the maximal multiplicative-type closed subgroup scheme $G^{\mu} = \operatorname{Spec} M$, together with its universal property, its functoriality for endomorphisms of $G$, and its compatibility with base change to henselian local $R$-algebras along local homomorphisms. It is used in the analysis of ordinary parts of Tate modules of Jacobians of modular curves and in the Cartier-duality computations for $p$-divisible groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Flat R H] :
    ∃ (M : Type v) (_ : CommRing M) (_ : HopfAlgebra R M) (_ : Coalgebra.IsCocomm R M)
      (_ : Module.Free R M) (_ : Module.Finite R M) (π : H →ₐc[R] M),
      Function.Surjective π ∧

      Algebra.Etale R (CartierDual R M) ∧

      (∀ (M' : Type v) [CommRing M'] [HopfAlgebra R M'] [Coalgebra.IsCocomm R M']
          [Module.Free R M'] [Module.Finite R M'] [Algebra.Etale R (CartierDual R M')]
          (f : H →ₐc[R] M'), ∃! g : M →ₐc[R] M', g.comp π = f) ∧

      (∀ φ : H →ₐc[R] H, ∃! ψ : M →ₐc[R] M, ψ.comp π = π.comp φ) ∧

      (∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
          IsLocalHom (algebraMap R R') →
          Algebra.Etale R' (CartierDual R' (R' ⊗[R] M)) ∧
          ∀ (N : Type v) [CommRing N] [HopfAlgebra R' N] [Coalgebra.IsCocomm R' N]
            [Module.Free R' N] [Module.Finite R' N] [Algebra.Etale R' (CartierDual R' N)]
            (f : R' ⊗[R] H →ₐc[R'] N),
              ∃! g : R' ⊗[R] M →ₐc[R'] N,
                g.comp (Bialgebra.TensorProduct.map (BialgHom.id R' R') π) = f) := by sorry
