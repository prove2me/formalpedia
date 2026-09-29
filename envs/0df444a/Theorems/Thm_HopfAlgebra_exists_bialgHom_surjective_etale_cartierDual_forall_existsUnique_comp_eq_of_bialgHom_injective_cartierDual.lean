-- Prove2me | Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual
-- name    : HopfAlgebra.exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/e3b9d225-cd4b-58ca-868e-8893b5549716
-- title:
--   Dualising an étale quotient of the Cartier dual
-- statement:
--   Let $R$ be a commutative ring and let $H$ be a commutative, cocommutative Hopf $R$-algebra that is finite and free as an $R$-module; write $\mathrm{CartierDual}\ R\ H$ for the $R$-linear dual $\mathrm{Hom}_R(H,R)$ with its induced bialgebra structure. Suppose given a commutative, cocommutative Hopf $R$-algebra $E$, finite and free over $R$, and a bialgebra homomorphism $\iota\colon E \to \mathrm{CartierDual}\ R\ H$ subject to: $\iota$ is injective; $E$ is étale as an $R$-algebra; $\iota$ is universal, in the sense that for every commutative, cocommutative Hopf $R$-algebra $E'$ which is finite and free over $R$ and étale over $R$, and every bialgebra homomorphism $f\colon E' \to \mathrm{CartierDual}\ R\ H$, there is a unique bialgebra homomorphism $g\colon E' \to E$ with $\iota \circ g = f$; the quotient of $\mathrm{CartierDual}\ R\ H$ by the image of the underlying $R$-linear map of $\iota$ is a free $R$-module; and, for every henselian local $R$-algebra $R'$ whose structure map $R \to R'$ is a local homomorphism, $R' \otimes_R E$ is étale over $R'$ and the base-changed map $\mathrm{id}_{R'} \otimes \iota\colon R' \otimes_R E \to R' \otimes_R \mathrm{CartierDual}\ R\ H$ has the corresponding universal property among commutative, cocommutative Hopf $R'$-algebras that are finite free and étale over $R'$. The conclusion asserts the existence of a commutative, cocommutative Hopf $R$-algebra $M$, finite and free as an $R$-module, together with a surjective bialgebra homomorphism $\pi\colon H \to M$, such that: $\mathrm{CartierDual}\ R\ M$ is étale over $R$; for every commutative, cocommutative Hopf $R$-algebra $M'$, finite and free over $R$ and with $\mathrm{CartierDual}\ R\ M'$ étale over $R$, every bialgebra homomorphism $f\colon H \to M'$ factors as $f = g \circ \pi$ for a unique bialgebra homomorphism $g\colon M \to M'$; every bialgebra endomorphism $\varphi$ of $H$ induces a unique bialgebra endomorphism $\psi$ of $M$ with $\psi \circ \pi = \pi \circ \varphi$; and for every henselian local $R$-algebra $R'$ with local structure map, $\mathrm{CartierDual}\ R'\ (R' \otimes_R M)$ is étale over $R'$ and the base-changed map $\mathrm{id}_{R'} \otimes \pi$ has the analogous factorisation property for bialgebra homomorphisms $R' \otimes_R H \to N$, with $N$ ranging over the commutative, cocommutative Hopf $R'$-algebras that are finite free over $R'$ and have étale Cartier dual.
--
--   This is the Cartier-duality step in the construction of the maximal subgroup of multiplicative type $G^{\mu} = ((G^{\vee})^{\mathrm{\acute{e}t}})^{\vee}$ of a finite locally free commutative group scheme $G = \mathrm{Spec}\,H$: an étale quotient datum for the Cartier dual is converted into a multiplicative-type subgroup datum for $G$, with no henselian or local hypothesis imposed on the base ring itself. It is used in the henselian-base form of the same statement, [`HopfAlgebra.exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing`](thm.html#HopfAlgebra.exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing), and the proof cites the biduality isomorphism [`CartierDual.exists_bialgEquiv_bidual`](thm.html#CartierDual.exists_bialgEquiv_bidual) and the compatibility of Cartier duality with base change [`CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul`](thm.html#CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual
    (R : Type u) [CommRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Free R H]

    (E : Type (max u v)) [CommRing E] [HopfAlgebra R E] [Coalgebra.IsCocomm R E]
    [Module.Free R E] [Module.Finite R E] (ι : E →ₐc[R] CartierDual R H)
    (hι : Function.Injective ι)
    (hE : Algebra.Etale R E)
    (huniv : ∀ (E' : Type (max u v)) [CommRing E'] [HopfAlgebra R E'] [Coalgebra.IsCocomm R E']
        [Module.Free R E'] [Module.Finite R E'] [Algebra.Etale R E']
        (f : E' →ₐc[R] CartierDual R H), ∃! g : E' →ₐc[R] E, ι.comp g = f)
    (hsplit : Module.Free R (CartierDual R H ⧸
      (LinearMap.range (ι : E →ₐ[R] CartierDual R H).toLinearMap : Submodule R (CartierDual R H))))
    (hbc : ∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
        IsLocalHom (algebraMap R R') →
        Algebra.Etale R' (R' ⊗[R] E) ∧
        ∀ (E' : Type (max u v)) [CommRing E'] [HopfAlgebra R' E'] [Coalgebra.IsCocomm R' E']
          [Module.Free R' E'] [Module.Finite R' E'] [Algebra.Etale R' E']
          (f : E' →ₐc[R'] R' ⊗[R] CartierDual R H),
            ∃! g : E' →ₐc[R'] R' ⊗[R] E,
              (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι).comp g = f) :
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
