-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector
-- name    : ModularCurve.JZeroNeronIdentityComponent.exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/4c5994ba-c20d-5876-a6e8-70d58ba36d07
-- title:
--   Eisenstein part of G[q^m] as Hecke-stable retract
-- statement:
--   Fix primes $p,q$ and a `JZeroNeronIdentityComponent p`, i.e. a smooth separated surjective group scheme $g\colon G\to\operatorname{Spec}\mathbb Z$ with connected fibres carrying a commutative relative group law $L$, a bijection `N.pts` from $\mathrm{Pic}^0$ of the modular function field of level $p$ over $\overline{\mathbb Q}$ onto the $\overline{\mathbb Q}$-points of $G$ compatible with addition, the Galois action and the Hecke action of `HeckeAlg` $=\mathbb Z[T_\ell:\ell$ prime$]$. The data are: an abelian sheaf $\mathcal G$ on the small fppf site of $\operatorname{Spec}\mathbb Z$ with identifications $e_{\mathcal G}$ of $\mathcal G(U)$ with the $U$-points of $G$, additive for $L$ and compatible with restriction; a ring homomorphism $\rho$ from `HeckeAlg` to $\operatorname{End}\mathcal G$ each of whose values is induced, on points and on sections, by an endomorphism of $G$ over $\mathbb Z$; a natural number $m$ with $J_0(p)[q^m]$ finite; an Eisenstein projector datum, namely $t_m\in$ `HeckeAlg` fixing exactly the elements of `eisensteinPrimaryTorsionBar p q m` (the $q^m$-torsion annihilated by some power of the Eisenstein ideal `eisensteinMaximalIdeal p q`) among $q^m$-torsion points, an endomorphism $\varphi_t$ of $G$ inducing $\rho(t_m)$ on points and sections, and an idempotent endomorphism $e_K$ of the kernel scheme $G[q^m]=\operatorname{pullback}$ of $L$-multiplication by $q^m$ along the unit section, compatible with $\varphi_t$ via the projection to $G$ and a group-law homomorphism for every relative group law on $G[q^m]$ for which the projection to $G$ is a homomorphism; and a geometric package, namely a closed immersion $j\colon E\to G[q^m]$ composing with the projection to a closed immersion $i\colon E\to G$, with $E$ affine, flat and locally of finite type over $\mathbb Z$, a commutative relative group law $L_E$ on $E$ for which $i$ is a homomorphism, the property that a $T$-point of $G[q^m]$ is fixed by $e_K$ precisely when it factors through $j$, the property that $x\in$ `eisensteinPrimaryTorsionBar p q m` iff `N.pts x` factors through $i$, a commutative ring $H$ with a $\mathbb Z$-Hopf algebra structure, of finite type and flat over $\mathbb Z$ and finite after tensoring with the subring of $\mathbb Q$ of rationals whose denominator is coprime to $\ell$ for every prime $\ell\neq p$, identifications `ePts` of `WithConv (H →ₐ[ℤ] T)` (the $\mathbb Z$-algebra homomorphisms $H\to T$ with their `WithConv` multiplication) with the $T$-points of $E$, multiplicative for $L_E$ and natural in $T$, and an abelian fppf sheaf $\mathcal J$ with additive identifications of $\mathcal J(U)$ with `Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤)))`, natural in $U$. The conclusion asserts the existence of morphisms $\iota\colon\mathcal J\to\ker(q^m\cdot\mathrm{id}_{\mathcal G})$ and $\pi\colon\ker(q^m\cdot\mathrm{id}_{\mathcal G})\to\mathcal J$ and an element $s$ of `HeckeAlg` such that $\iota$ followed by $\pi$ is the identity of $\mathcal J$, $s\notin$ `eisensteinMaximalIdeal p q`, the endomorphism of $\ker(q^m\cdot\mathrm{id}_{\mathcal G})$ induced by $\rho(s)$ equals $\pi$ followed by $\iota$, the endomorphism induced by $\rho(t)$ commutes with $\pi$ followed by $\iota$ for every $t$, the composite of $\iota$, the endomorphism induced by $\rho(t)$ and $\pi$ is an isomorphism for every $t\notin$ `eisensteinMaximalIdeal p q`, and, on sections over each $U$, the $U$-point of $G$ attached to the image of $x\in\mathcal J(U)$ under $\iota$ followed by the kernel inclusion is the canonical morphism $U\to\operatorname{Spec}\Gamma(U,\mathcal O_U)$, followed by the $\Gamma(U,\mathcal O_U)$-point of $E$ corresponding to $x$, followed by $i$.
--
--   This is the sheaf-theoretic form of the statement that the Eisenstein-primary part of the $q^m$-torsion of the Néron identity component of $J_0(p)$ splits off, as a Hecke-stable retract cut out by a Hecke element acting as an idempotent away from the Eisenstein ideal, and is represented by the finite flat group scheme $E$ with Hopf algebra $H$. It feeds the passage from the Eisenstein projector datum and the geometric package to the comparison of fppf cohomology localised at the Eisenstein ideal, and is used in the construction of the Hopf-order torsion core of $J_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronIdentityComponent_exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.JZeroNeronIdentityComponent.exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (N : JZeroNeronIdentityComponent p)

    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e𝒢 : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e𝒢 U (s + s') = N.L.mul U.hom (e𝒢 U s) (e𝒢 U s'))
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e𝒢 U (𝒢.1.map k.op s) = GoodReductionJacobian.schemeHomOverComp k.left (MorphismProperty.Over.w k) (e𝒢 V s))
    (ρ : letI := heckeModuleBar p; HeckeAlg →+* End 𝒢)
    (hρ : letI := heckeModuleBar p
      ∀ t : HeckeAlg, ∃ φ : SchemeHomOver N.g N.g,
        (∀ x : JZero p, (N.pts (t • x)).1 = (N.pts x).1 ≫ φ.1) ∧
        ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e𝒢 U ((ρ t).1.app (op U) s)).1 = (e𝒢 U s).1 ≫ φ.1)
    (m : ℕ) (hfin : Finite ↥(jZeroTorsion p (q ^ m)))

    (tm : letI := heckeModuleBar p; HeckeAlg) (φt : SchemeHomOver N.g N.g)
    (eK : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g))
    (ht : letI := heckeModuleBar p
      ∀ x : JZero p, (q ^ m : ℤ) • x = 0 → (tm • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m))
    (heK_idem : eK.1 ≫ eK.1 = eK.1)
    (hφt_pts : letI := heckeModuleBar p; ∀ x : JZero p, (N.pts (tm • x)).1 = (N.pts x).1 ≫ φt.1)
    (hφt_sec : ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e𝒢 U ((ρ tm).1.app (op U) s)).1 = (e𝒢 U s).1 ≫ φt.1)
    (heφ : eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φt.1)
    (heK_hom : ∀ (LK : RelativeGroupLaw ℤ (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
      (∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) (⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) N.g) =
          N.L.mul s (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩)) →
      ∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) eK =
          LK.mul s (NeronModelInfra.schemeHomOverComp x eK) (NeronModelInfra.schemeHomOverComp y eK))

    (E : Scheme.{0}) (gX : E ⟶ (Spec (CommRingCat.of ℤ))) (i : E ⟶ N.G) (j : E ⟶ N.L.schemeKer (q ^ m))
    (LE : RelativeGroupLaw ℤ gX)
    (hi : i ≫ N.g = gX) [IsClosedImmersion i] (hj : j ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = i) [IsClosedImmersion j]
    [IsAffineHom gX] [Flat gX] [LocallyOfFiniteType gX]
    (hfix : ∀ (hj' : j ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g = gX) {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
      NeronModelInfra.schemeHomOverComp x eK = x ↔
        ∃ y : SchemeHomOver s gX, NeronModelInfra.schemeHomOverComp y (⟨j, hj'⟩ : SchemeHomOver gX (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)) = x)
    (hcommE : ∀ {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t gX), LE.mul t x y = LE.mul t y x)
    (hi_hom : ∀ (hi' : i ≫ N.g = gX) {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t gX),
      NeronModelInfra.schemeHomOverComp (LE.mul t x y) (⟨i, hi'⟩ : SchemeHomOver gX N.g) =
        N.L.mul t (NeronModelInfra.schemeHomOverComp x ⟨i, hi'⟩) (NeronModelInfra.schemeHomOverComp y ⟨i, hi'⟩))
    (hpts : ∀ x : JZero p, x ∈ eisensteinPrimaryTorsionBar p q m ↔
      ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) gX, y.1 ≫ i = (N.pts x).1)
    (H : Type) [CommRing H] [HopfAlgebra ℤ H] [Algebra.FiniteType ℤ H] [Module.Flat ℤ H]
    (hHff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) H))
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) gX)
    (hePts_mul : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H →ₐ[ℤ] T)),
      ePts T (φ * ψ) = LE.mul _ (ePts T φ) (ePts T ψ))
    (hePts_nat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
        (σ : T →ₐ[ℤ] T') (φ : WithConv (H →ₐ[ℤ] T)),
      (ePts T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts T φ).1)
    (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (sE : ∀ U : specInt.Fppf, 𝒥.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (hsE : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : 𝒥.1.obj (op V)) (h : H),
      (Additive.toMul (sE U (𝒥.1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (sE V s)) h)) :
    letI := heckeModuleBar p
    ∃ (ι : 𝒥 ⟶ kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) (π : kernel (((q : ℤ) ^ m) • 𝟙 𝒢) ⟶ 𝒥) (s : HeckeAlg),
      ι ≫ π = 𝟙 𝒥 ∧
      s ∉ eisensteinMaximalIdeal p q ∧
      (∃ w : (((q : ℤ) ^ m) • 𝟙 𝒢) ≫ ρ s = ρ s ≫ (((q : ℤ) ^ m) • 𝟙 𝒢),
        kernel.map (((q : ℤ) ^ m) • 𝟙 𝒢) (((q : ℤ) ^ m) • 𝟙 𝒢) (ρ s) (ρ s) w = π ≫ ι) ∧
      (∀ t : HeckeAlg, ∃ w : (((q : ℤ) ^ m) • 𝟙 𝒢) ≫ ρ t = ρ t ≫ (((q : ℤ) ^ m) • 𝟙 𝒢),
        kernel.map (((q : ℤ) ^ m) • 𝟙 𝒢) (((q : ℤ) ^ m) • 𝟙 𝒢) (ρ t) (ρ t) w ≫ (π ≫ ι)
          = (π ≫ ι) ≫ kernel.map (((q : ℤ) ^ m) • 𝟙 𝒢) (((q : ℤ) ^ m) • 𝟙 𝒢) (ρ t) (ρ t) w) ∧
      (∀ t : HeckeAlg, t ∉ eisensteinMaximalIdeal p q →
        ∃ w : (((q : ℤ) ^ m) • 𝟙 𝒢) ≫ ρ t = ρ t ≫ (((q : ℤ) ^ m) • 𝟙 𝒢),
          IsIso (ι ≫ kernel.map (((q : ℤ) ^ m) • 𝟙 𝒢) (((q : ℤ) ^ m) • 𝟙 𝒢) (ρ t) (ρ t) w ≫ π)) ∧

      (∀ (U : specInt.Fppf) (x : 𝒥.1.obj (op U)),
        (e𝒢 U ((kernel.ι (((q : ℤ) ^ m) • 𝟙 𝒢)).1.app (op U) (ι.1.app (op U) x))).1 =
          U.left.toSpecΓ ≫ (ePts Γ(U.left, ⊤) (Additive.toMul (sE U x))).1 ≫ i) := by sorry
