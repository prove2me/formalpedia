-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_rid_map_counit_coaction_eq_of_points_formula
-- name    : GoodReductionJacobian.RelativeGroupLaw.rid_map_counit_coaction_eq_of_points_formula
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/b83ec859-b1ce-5219-9e77-a3ffa1b43e0f
-- title:
--   Counit identity for the chart coaction ρ_U
-- statement:
--   Fix a field $K$, a scheme $A$ and a morphism $f : A \to \operatorname{Spec} K$, together with a relative group law $L$ on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \text{ over } \operatorname{Spec} K\}$, natural under base change), assumed commutative, and a bundle $hA$ recording that $f$ is smooth and proper with connected fibres and admits a group law. Let $n \in \mathbb{N}$ and assume the endomorphism $[n] =$ `L.schemeNsmul n` of $A$ (the $n$-fold $L$-multiple of the identity point) is finite, flat and surjective. Let $H$ be a commutative ring which is a finite cocommutative $K$-Hopf algebra, and let $e$ identify, for every commutative $K$-algebra $T$, the convolution monoid of $K$-algebra maps $H \to T$ with the set of $T$-points $x$ of $A$ satisfying $n\cdot x = 0$; $e$ is assumed multiplicative (`he_mul`) and natural in $T$ (`he_nat`). Let $\mathrm{act} : A \times_{\operatorname{Spec} K} \operatorname{Spec} H \to A$ be a morphism over $f$ (via the first projection) which on points is translation, $\mathrm{act}(x,\varphi) = x \cdot_L e_T(\varphi)$ (`hpts`), which commutes with $[n]$ in the sense $\mathrm{fst} \mathbin{;} [n] = \mathrm{act} \mathbin{;} [n]$, and for which the induced morphism to $A \times_{[n],A,[n]} A$ is an isomorphism. Sections of $A$ and of the pullback carry the $K$-algebra structures coming from their structure morphisms. Assume further: $[n]^{-1}U$ is affine open for every affine open $U$ of $A$; chart isomorphisms $\varepsilon_V : \Gamma(A \times_{\operatorname{Spec} K} \operatorname{Spec} H, \mathrm{fst}^{-1}V) \xrightarrow{\ \sim\ } \Gamma(A,V) \otimes_K H$ of $K$-algebras for affine open $V$, sending $\mathrm{fst}^{\#}a$ to $a \otimes 1$ and $\mathrm{snd}^{\#}h$ to $1 \otimes h$ and compatible with restriction along $V' \le V$; the inclusion $\mathrm{fst}^{-1}([n]^{-1}U) \le \mathrm{act}^{-1}([n]^{-1}U)$; and $K$-algebra maps $\rho_U : \Gamma(A,[n]^{-1}U) \to \Gamma(A,[n]^{-1}U) \otimes_K H$ given by $\varepsilon_{[n]^{-1}U}$ applied to the map on sections induced by $\mathrm{act}$. Then for every affine open $U$ and every $s \in \Gamma(A,[n]^{-1}U)$, applying $\mathrm{id} \otimes \varepsilon_H$ to $\rho_U(s)$ and then the canonical isomorphism $\Gamma(A,[n]^{-1}U) \otimes_K K \cong \Gamma(A,[n]^{-1}U)$ returns $s$.
--
--   This is the counit axiom for the comodule algebra structure $\rho_U$ by which the finite Hopf algebra $H$ of $n$-torsion coacts on the charts $\Gamma(A,[n]^{-1}U)$, expressing that translation by the identity point acts trivially. It is one half of [`GoodReductionJacobian.RelativeGroupLaw.coaction_counit_and_coassoc_of_points_formula`](thm.html#GoodReductionJacobian.RelativeGroupLaw.coaction_counit_and_coassoc_of_points_formula), which combines it with coassociativity to exhibit $[n] : A \to A$ locally as an $H$-Galois (torsor) covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_rid_map_counit_coaction_eq_of_points_formula.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.rid_map_counit_coaction_eq_of_points_formula
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
        (Algebra.TensorProduct.rid K K _) (Algebra.TensorProduct.map (AlgHom.id K _) (Bialgebra.counitAlgHom K H) (ρ U s)) = s := by sorry
