-- Prove2me | Theorems.Thm_IsLocalRing_exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete
-- name    : IsLocalRing.exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/f2bac849-77e6-547a-9cf4-05cff95941b5
-- title:
--   Yoneda for pro-representable functors on Artinian local O-algebras
-- statement:
--   Let $O$ be a commutative local ring with residue field $k = \mathrm{ResidueField}(O)$, let $S$ be a commutative ring equipped with a ring homomorphism $\bar x \colon S \to k$, and let $R$ be a Noetherian local commutative $O$-algebra which is adically complete for its maximal ideal, together with a ring homomorphism $\mathrm{res}_R \colon R \to k$ satisfying $\mathrm{res}_R \circ (\text{structure map } O \to R) =$ the residue map of $O$. Suppose given, for every Artinian local commutative $O$-algebra $A$ with a surjective ring homomorphism $\mathrm{res}_A \colon A \to k$ compatible with the residue map of $O$, a map $\beta$ sending each ring homomorphism $\psi \colon S \to A$ with $\mathrm{res}_A \circ \psi = \bar x$ to an $O$-algebra homomorphism $R \to A$, such that: $\mathrm{res}_A \circ \beta(\psi) = \mathrm{res}_R$ always holds; $\beta$ is injective in $\psi$ for each such $A$; every $O$-algebra homomorphism $\chi \colon R \to A$ with $\mathrm{res}_A \circ \chi = \mathrm{res}_R$ is of the form $\beta(\psi)$ for some admissible $\psi$; and $\beta$ is natural, in the sense that for every $O$-algebra homomorphism $f \colon A \to A'$ between two such objects with $\mathrm{res}_{A'} \circ f = \mathrm{res}_A$ one has $\beta(f \circ \psi) = f \circ \beta(\psi)$. The conclusion is that there exists a ring homomorphism $\varphi \colon S \to R$ with $\mathrm{res}_R \circ \varphi = \bar x$ such that, for every $A$, $\mathrm{res}_A$ as above and every $\psi \colon S \to A$ with $\mathrm{res}_A \circ \psi = \bar x$, there is a unique $O$-algebra homomorphism $\chi \colon R \to A$ with $\mathrm{res}_A \circ \chi = \mathrm{res}_R$ and $\chi \circ \varphi = \psi$; and moreover that this unique $\chi$ is the given $\beta(\psi)$, i.e. $\beta(\psi) \circ \varphi = \psi$ for all such $A$ and $\psi$.
--
--   This is the Yoneda lemma for pro-objects in the form used in deformation theory: a functor of Artinian local $O$-algebras with residue field $k$ that is isomorphic to the functor of points of a complete Noetherian local $O$-algebra $R$ is pro-represented by $R$, and the universal element $\varphi \colon S \to R$ is obtained from the elements attached to the Artinian quotients $R/\mathfrak m^{n+1}$. It is used in the comparison of the stalk of a fine moduli problem for quaternionic Shimura curves with a universal deformation ring, via [`CerednikDrinfeld.QM.IsFineModuli.exists_ringHom_stalk_forall_existsUnique_algHom_of_prorepresents_deformations`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_ringHom_stalk_forall_existsUnique_algHom_of_prorepresents_deformations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing in

theorem IsLocalRing.exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete
    (O : Type) [CommRing O] [IsLocalRing O]
    (S : Type) [CommRing S] (xbar : S →+* ResidueField O)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    [IsAdicComplete (maximalIdeal R) R]
    (resR : R →+* ResidueField O) (hresR : resR.comp (algebraMap O R) = residue O)
    (β : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
        ∀ ψ : S →+* A, resA.comp ψ = xbar → (R →ₐ[O] A))
    (hβ_res : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O) (ψ : S →+* A) (hψ : resA.comp ψ = xbar),
        resA.comp (β A resA hs hc ψ hψ).toRingHom = resR)
    (hβ_inj : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (ψ₁ : S →+* A) (hψ₁ : resA.comp ψ₁ = xbar) (ψ₂ : S →+* A) (hψ₂ : resA.comp ψ₂ = xbar),
        β A resA hs hc ψ₁ hψ₁ = β A resA hs hc ψ₂ hψ₂ → ψ₁ = ψ₂)
    (hβ_surj : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O) (χ : R →ₐ[O] A),
        resA.comp χ.toRingHom = resR → ∃ (ψ : S →+* A) (hψ : resA.comp ψ = xbar), β A resA hs hc ψ hψ = χ)
    (hβ_nat : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (A' : Type) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
        (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA')
        (hc' : resA'.comp (algebraMap O A') = residue O)
        (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA →
        ∀ (ψ : S →+* A) (hψ : resA.comp ψ = xbar) (hψ' : resA'.comp (f.toRingHom.comp ψ) = xbar),
        β A' resA' hs' hc' (f.toRingHom.comp ψ) hψ' = f.comp (β A resA hs hc ψ hψ)) :
    ∃ φ : S →+* R, resR.comp φ = xbar ∧
      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O), Function.Surjective resA →
          resA.comp (algebraMap O A) = residue O →
        ∀ ψ : S →+* A, resA.comp ψ = xbar →
          ∃! χ : R →ₐ[O] A, resA.comp χ.toRingHom = resR ∧ χ.toRingHom.comp φ = ψ) ∧
      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (ψ : S →+* A) (hψ : resA.comp ψ = xbar),
        (β A resA hs hc ψ hψ).toRingHom.comp φ = ψ) := by sorry
