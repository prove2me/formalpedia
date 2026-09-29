-- Prove2me | Theorems.Thm_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField
-- name    : HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/10b8835a-e4f7-5ead-9d7a-fa8a29a0b301
-- title:
--   Lifting the étale quotient to a henselian local base
-- statement:
--   Let $R$ be a henselian local commutative ring with residue field $k =$ `IsLocalRing.ResidueField R`, and let $H$ be a commutative ring carrying a Hopf $R$-algebra structure whose comultiplication is cocommutative, and which is finite and flat as an $R$-module. Assume given the étale quotient of the special fibre in the following form: a commutative ring $E_0$ with a cocommutative Hopf $k$-algebra structure, finite as a $k$-module and étale over $k$, an injective bialgebra homomorphism $\iota_0 \colon E_0 \to k \otimes_R H$ over $k$, such that (i) for every commutative ring $E'$ with a cocommutative Hopf $k$-algebra structure that is finite over $k$ and étale over $k$, and every bialgebra homomorphism $f \colon E' \to k \otimes_R H$, there is a unique bialgebra homomorphism $g \colon E' \to E_0$ with $\iota_0 \circ g = f$; and (ii) for every field $K$ (in the universe of $R$) with a $k$-algebra structure, every finite étale cocommutative Hopf $K$-algebra $E'$ and every bialgebra homomorphism $f \colon E' \to K \otimes_k (k \otimes_R H)$, there is a unique bialgebra homomorphism $g \colon E' \to K \otimes_k E_0$ with $(\mathrm{id}_K \otimes \iota_0) \circ g = f$. Then there exist a commutative ring $E$ (in the universe of $H$) with a cocommutative Hopf $R$-algebra structure, free and finite as an $R$-module, and an injective bialgebra homomorphism $\iota \colon E \to H$ over $R$, such that: $E$ is étale over $R$; every bialgebra homomorphism $f \colon E' \to H$ from a finite free étale cocommutative Hopf $R$-algebra $E'$ factors as $f = \iota \circ g$ for a unique bialgebra homomorphism $g \colon E' \to E$; every bialgebra endomorphism $\varphi$ of $H$ satisfies $\iota \circ \psi = \varphi \circ \iota$ for a unique bialgebra endomorphism $\psi$ of $E$; the quotient of $H$ by the image of the underlying $R$-linear map of $\iota$ is a free $R$-module; and for every henselian local commutative $R$-algebra $R'$ (in the universe of $R$) for which $R \to R'$ is a local homomorphism, $R' \otimes_R E$ is étale over $R'$ and, for every finite free étale cocommutative Hopf $R'$-algebra $E'$ and every bialgebra homomorphism $f \colon E' \to R' \otimes_R H$, there is a unique bialgebra homomorphism $g \colon E' \to R' \otimes_R E$ with $(\mathrm{id}_{R'} \otimes \iota) \circ g = f$.
--
--   In the dual language of finite flat commutative group schemes $G = \operatorname{Spec} H$ over a henselian local base, this is the lifting step in the construction of the connected–étale sequence $0 \to G^0 \to G \to G^{\mathrm{\acute e}t} \to 0$: the hypotheses are the corresponding assertion for the special fibre $G_k$, and the conclusion the assertion over $R$, including functoriality in endomorphisms of $G$, freeness of the coordinate ring of $G^0$-coinvariants, and stability under henselian local base change. It is used to obtain the statement over a henselian local ring with no hypothesis on the special fibre, via the field case; the proof invokes the existence of an étale Hopf $R$-algebra with prescribed residue fibre and the unique lifting of bialgebra homomorphisms out of a finite étale Hopf algebra over a henselian local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Flat R H]

    (E₀ : Type (max u v)) [CommRing E₀] [HopfAlgebra (IsLocalRing.ResidueField R) E₀]
    [Coalgebra.IsCocomm (IsLocalRing.ResidueField R) E₀] [Module.Finite (IsLocalRing.ResidueField R) E₀]
    (ι₀ : E₀ →ₐc[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] H)
    (hι₀ : Function.Injective ι₀)
    (hE₀ : Algebra.Etale (IsLocalRing.ResidueField R) E₀)
    (huniv₀ : ∀ (E' : Type (max u v)) [CommRing E'] [HopfAlgebra (IsLocalRing.ResidueField R) E']
        [Coalgebra.IsCocomm (IsLocalRing.ResidueField R) E'] [Module.Finite (IsLocalRing.ResidueField R) E']
        [Algebra.Etale (IsLocalRing.ResidueField R) E']
        (f : E' →ₐc[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] H),
        ∃! g : E' →ₐc[IsLocalRing.ResidueField R] E₀, ι₀.comp g = f)
    (hbc₀ : ∀ (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField R) K]
        (E' : Type (max u v)) [CommRing E'] [HopfAlgebra K E'] [Coalgebra.IsCocomm K E']
        [Module.Finite K E'] [Algebra.Etale K E']
        (f : E' →ₐc[K] K ⊗[IsLocalRing.ResidueField R] (IsLocalRing.ResidueField R ⊗[R] H)),
        ∃! g : E' →ₐc[K] K ⊗[IsLocalRing.ResidueField R] E₀,
          (Bialgebra.TensorProduct.map (BialgHom.id K K) ι₀).comp g = f) :
    ∃ (E : Type v) (_ : CommRing E) (_ : HopfAlgebra R E) (_ : Coalgebra.IsCocomm R E)
      (_ : Module.Free R E) (_ : Module.Finite R E) (ι : E →ₐc[R] H),
      Function.Injective ι ∧

      Algebra.Etale R E ∧

      (∀ (E' : Type v) [CommRing E'] [HopfAlgebra R E'] [Coalgebra.IsCocomm R E']
          [Module.Free R E'] [Module.Finite R E'] [Algebra.Etale R E']
          (f : E' →ₐc[R] H), ∃! g : E' →ₐc[R] E, ι.comp g = f) ∧

      (∀ φ : H →ₐc[R] H, ∃! ψ : E →ₐc[R] E, ι.comp ψ = φ.comp ι) ∧

      Module.Free R (H ⧸ LinearMap.range (ι : E →ₐ[R] H).toLinearMap) ∧

      (∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
          IsLocalHom (algebraMap R R') →
          Algebra.Etale R' (R' ⊗[R] E) ∧
          ∀ (E' : Type v) [CommRing E'] [HopfAlgebra R' E'] [Coalgebra.IsCocomm R' E']
            [Module.Free R' E'] [Module.Finite R' E'] [Algebra.Etale R' E']
            (f : E' →ₐc[R'] R' ⊗[R] H),
              ∃! g : E' →ₐc[R'] R' ⊗[R] E,
                (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι).comp g = f) := by sorry
