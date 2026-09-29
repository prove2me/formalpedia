-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_assoc_map_coaction_coaction_eq_map_comul_of_points_formula
-- name    : GoodReductionJacobian.RelativeGroupLaw.assoc_map_coaction_coaction_eq_map_comul_of_points_formula
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/5bf93bf7-e04e-5a5d-a1d8-5dcf216f5322
-- title:
--   Coassociativity of the chart coaction ρ_U
-- statement:
--   Let $K$ be a field, $f\colon A\to\operatorname{Spec}K$ a scheme over $K$, and $L$ a relative group law on $f$: a functorial group structure on the sets $\{\varphi\colon T\to A \mid \varphi\circ(\cdot)=t\}$ of $T$-points over $\operatorname{Spec}K$, natural in $T$. Assume $L$ is commutative, that $f$ satisfies `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a relative group law exists), and fix $n\in\mathbb N$ such that the morphism $[n]=$ `L.schemeNsmul n`$\colon A\to A$ (the $n$-fold sum of the identity point) is finite, flat and surjective. Let $H$ be a commutative Hopf algebra over $K$, finite as a $K$-module, with cocommutative comultiplication, together with bijections $e_T\colon \mathrm{WithConv}(H\to_{\mathrm{alg}}T)\to\{x : \ n\cdot x = 0\}$ onto the $n$-torsion $T$-points of $L$, for all commutative $K$-algebras $T$, which are multiplicative for the convolution product (`he_mul`) and natural in $T$ (`he_nat`). Let $\mathrm{act}\colon A\times_{K}\operatorname{Spec}H\to A$ be a morphism over $K$ (`hact`) that on points is translation, $\mathrm{act}(x,\varphi)=x+e_T(\varphi)$ (`hpts`), compatible with $[n]$ (`hsh`) and inducing an isomorphism onto the pullback of $[n]$ along $[n]$ (`hiso`). Equip sections of $A$ and of the pullback with the $K$-algebra structures coming from $f$ and from the first projection followed by $f$. Assume $[n]^{-1}U$ is affine for every affine open $U$, and let $\varepsilon_V\colon \Gamma(A\times_K\operatorname{Spec}H,\ \mathrm{fst}^{-1}V)\xrightarrow{\ \sim\ }\Gamma(A,V)\otimes_K H$ be $K$-algebra isomorphisms for affine open $V$, carrying $\mathrm{fst}^*a$ to $a\otimes 1$, compatible with restriction, and carrying $\mathrm{snd}^*h$ to $1\otimes h$. Let $\rho_U\colon\Gamma(A,[n]^{-1}U)\to\Gamma(A,[n]^{-1}U)\otimes_K H$ be the $K$-algebra maps given by $\varepsilon$ composed with the restriction of $\mathrm{act}^{\sharp}$ (the inclusion of preimages being hypothesis `hle`). Then for every affine open $U$ of $A$ and every $s\in\Gamma(A,[n]^{-1}U)$, after the associativity isomorphism of tensor products, $(\rho_U\otimes\mathrm{id}_H)(\rho_U(s))=(\mathrm{id}\otimes\Delta_H)(\rho_U(s))$.
--
--   This is the coassociativity half of the statement that $\rho_U$ makes the chart algebra $\Gamma(A,[n]^{-1}U)$ a comodule over the Hopf algebra $H$, i.e. that translation by the $n$-torsion scheme $\operatorname{Spec}H$ is an action in the ring-theoretic dictionary. It is used, together with the counit identity, by [`GoodReductionJacobian.RelativeGroupLaw.coaction_counit_and_coassoc_of_points_formula`](thm.html#GoodReductionJacobian.RelativeGroupLaw.coaction_counit_and_coassoc_of_points_formula) in the construction of the quotient of $A$ by its $n$-torsion and the identification of $[n]$ as the associated faithfully flat covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_assoc_map_coaction_coaction_eq_map_comul_of_points_formula.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.assoc_map_coaction_coaction_eq_map_comul_of_points_formula
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n))
    (hsurj : Function.Surjective (L.schemeNsmul n))
    (H : Type u) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)
    (act : pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ⟶ A)
    (hact : act ≫ f = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ f)
    (hpts : ∀ (T : Type u) [CommRing T] [Algebra K T]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f) (φ : WithConv (H →ₐ[K] T))
        (hx : x.1 ≫ f = Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K H))),
      pullback.lift x.1 (Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T))) hx ≫ act =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap K T))) x (e T φ).val).1)
    (hsh : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ L.schemeNsmul n = act ≫ L.schemeNsmul n)
    (hiso : IsIso (pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) act hsh))
    :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens, Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W
    ∀ (hNaff : ∀ U : A.affineOpens, IsAffineOpen ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)))
    (ε : ∀ (V : A.Opens) (_ : IsAffineOpen V), Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H)
    (hε_fst : ∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)),
      ε V hV (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H))
    (hε_res : ∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
        (s : Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
        ε V' hV' (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).preimage_mono hle)).op).hom s))
    (hε_snd : ∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
      ε V hV (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) =
        (1 : Γ(A, V)) ⊗ₜ[K] h)
    (hle : ∀ U : A.affineOpens, (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ≤ act ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)))
    (ρ : ∀ U : A.affineOpens, Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
    (hρ : ∀ (U : A.affineOpens) (s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))),
      ρ U s = ε ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) (hNaff U) ((act.appLE ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))) (hle U)).hom s))
    (U : A.affineOpens),
    ∀ s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)),
        (Algebra.TensorProduct.assoc K K K _ H H) (Algebra.TensorProduct.map (ρ U) (AlgHom.id K H) (ρ U s)) =
          Algebra.TensorProduct.map (AlgHom.id K _) (Bialgebra.comulAlgHom K H) (ρ U s) := by sorry
