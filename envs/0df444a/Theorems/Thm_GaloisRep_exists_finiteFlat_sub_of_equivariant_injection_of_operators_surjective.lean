-- Prove2me | Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection_of_operators_surjective
-- name    : GaloisRep.exists_finiteFlat_sub_of_equivariant_injection_of_operators_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/96483b6a-4422-5646-9b71-928c7b8c1b56
-- title:
--   Finite flat Hopf quotient realising a stable subgroup of points
-- statement:
--   Fix a natural number $p$ and write $R$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $G$ be a commutative ring carrying a Hopf algebra structure over $R$ which is module-finite, flat and cocommutative over $R$; let $M$ be an abelian group with a distributive action of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \mathrm{AlgebraicClosure}\ \mathbb{Q} \simeq_{\mathbb{Q}} \mathrm{AlgebraicClosure}\ \mathbb{Q}$. Assume given a bijection $e$ from the $R$-algebra maps $G \to \overline{\mathbb{Q}}$, equipped with their convolution monoid structure (`WithConv`), to $M$ which turns convolution into addition, and which is Galois-equivariant in the sense that $g = \sigma \circ f$ pointwise on $G$ forces $e\,g = \sigma \cdot e\,f$. Assume further a family of additive endomorphisms $\mathrm{act}\,t$ of $M$ indexed by a type $T$, realised by $R$-algebra endomorphisms $\varphi\,t$ of $G$ which carry the augmentation ideal (the kernel of the counit) into itself, in the sense that $g = f \circ \varphi\,t$ pointwise forces $e\,g = \mathrm{act}\,t\,(e\,f)$. Finally let $N$ be an abelian group with a Galois action, $\iota : N \to M$ an injective Galois-equivariant additive map, and $\mathrm{act}_N\,t$ additive endomorphisms of $N$ with $\iota \circ \mathrm{act}_N\,t = \mathrm{act}\,t \circ \iota$. The conclusion asserts the existence of a commutative ring $H$ with a Hopf algebra structure over $R$, module-finite, flat and cocommutative over $R$, together with a bijection $e'$ from the convolution monoid of $R$-algebra maps $H \to \overline{\mathbb{Q}}$ to $N$ that is additive and Galois-equivariant in the same sense; a surjective bialgebra map $q : G \to H$ over $R$ such that whenever $g = f \circ q$ pointwise one has $\iota(e'\,f) = e\,g$; and $R$-algebra endomorphisms $\varphi'\,t$ of $H$ preserving the augmentation ideal which realise $\mathrm{act}_N\,t$ through $e'$ in the same way. No primality hypothesis on $p$ is imposed.
--
--   This is the passage from a Galois- and operator-stable subgroup $N$ of the $\overline{\mathbb{Q}}$-points of a finite flat commutative cocommutative Hopf algebra over $\mathbb{Z}_{(p)}$ to a finite flat Hopf quotient whose points are exactly that subgroup, with the operators descending; in scheme language, the scheme-theoretic closure of a stable subgroup of the generic fibre. It is used to produce finite flat models carrying Hecke, Frobenius and Verschiebung operators for torsion subgroups arising from modular curves, and in the analysis of level actions on finite flat Hopf algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection_of_operators_surjective.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FiniteFlat_ClosureHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.exists_finiteFlat_sub_of_equivariant_injection_of_operators_surjective (p : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra (GaloisRep.ratLocalizedAt p) G]
    [Module.Finite (GaloisRep.ratLocalizedAt p) G] [Module.Flat (GaloisRep.ratLocalizedAt p) G]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G]
    {M : Type} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    {T : Type} (act : T → M →+ M)
    (φ : T → (G →ₐ[GaloisRep.ratLocalizedAt p] G))
    (hφ_aug : ∀ t : T,
      RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) G) ≤
        (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) G)).comap (φ t))
    (hφ : ∀ (t : T) (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : G, g x = f (φ t x)) → e g = act t (e f))
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (ι : N →+ M) (hι : Function.Injective ι)
    (hι_eq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : N), ι (σ • n) = σ • (ι n))
    (actN : T → N →+ N) (hι_act : ∀ (t : T) (n : N), ι (actN t n) = act t (ι n)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → e' g = σ • (e' f)) ∧
        (∃ q : G →ₐc[GaloisRep.ratLocalizedAt p] H, Function.Surjective q ∧
          ∀ (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))
            (g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ x : G, g x = f (q x)) → ι (e' f) = e g) ∧
        ∃ φ' : T → (H →ₐ[GaloisRep.ratLocalizedAt p] H),
          (∀ t : T,
            RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H) ≤
              (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H)).comap (φ' t)) ∧
          ∀ (t : T) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ x : H, g x = f (φ' t x)) → e' g = actN t (e' f) := by sorry
