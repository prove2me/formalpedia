-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/3982cc05-3cd2-5d52-b8df-68f2ff0e8d73
-- title:
--   Hopf points sheaf as a retract of G[n]
-- statement:
--   Let $f\colon A\to\operatorname{Spec}\mathbb Z$ be a scheme morphism carrying a relative group law $G$ (a functorial group structure on the sets $\{\phi\colon T\to A \mid \phi\text{ followed by }f = t\}$ of $T$-points over $\operatorname{Spec}\mathbb Z$, natural in $T$), assumed commutative, and let $\mathcal G$ be a sheaf of abelian groups on the small fppf site of $\operatorname{Spec}\mathbb Z$ (objects: schemes over $\operatorname{Spec}\mathbb Z$ that are flat and locally of finite presentation) together with bijections $e_U\colon\mathcal G(U)\to\{U\text{-points of }A\}$ sending addition to $G$'s multiplication and commuting with restriction. Let $k\in\mathbb N$, $n\in\mathbb Z$ with $n=k$, let $\rho_s\colon\mathcal G\to\mathcal G$ be an endomorphism acting on sections by post-composition with an endomorphism $\varphi$ of $A$ over $\operatorname{Spec}\mathbb Z$, and let $eKm$ be an endomorphism of the kernel scheme $A[k]=A\times_{[k],\,e}\operatorname{Spec}\mathbb Z$ over $\operatorname{Spec}\mathbb Z$ which is idempotent, whose composite with the first projection $A[k]\to A$ equals that projection followed by $\varphi$, and which, for every relative group law $LK$ on $A[k]$ for which the projection to $A$ is a homomorphism of point-functors, is itself a homomorphism for $LK$. Let $E\to\operatorname{Spec}\mathbb Z$ be affine, flat and locally of finite type, with a commutative relative group law $LE$, closed immersions $i\colon E\to A$ over $\operatorname{Spec}\mathbb Z$ and $j\colon E\to A[k]$ with $j$ followed by the projection equal to $i$, such that $i$ is a homomorphism from $LE$ to $G$ on points, and such that a $T$-point $x$ of $A[k]$ satisfies $x$ followed by $eKm$ equal to $x$ exactly when $x$ factors through $j$. Let $H$ be a commutative ring with a Hopf algebra structure over $\mathbb Z$, equipped with bijections $\mathrm{ePts}_T$ from the convolution monoid of $\mathbb Z$-algebra maps $H\to T$ to the $T$-points of $E$, multiplicative for $LE$ and natural in $T$; and let $\mathcal J$ be a second fppf sheaf of abelian groups with additive equivalences $\mathcal J(U)\cong\operatorname{Hom}_{\mathbb Z\text{-alg}}(H,\Gamma(U,\mathcal O_U))$ under convolution, compatible with restriction via $\Gamma$. Then there exist morphisms $\iota\colon\mathcal J\to\ker(n\cdot\mathrm{id}_{\mathcal G})$ and $\pi\colon\ker(n\cdot\mathrm{id}_{\mathcal G})\to\mathcal J$, and $\rho_s$ commutes with $n\cdot\mathrm{id}_{\mathcal G}$, such that $\iota$ followed by $\pi$ is the identity of $\mathcal J$, $\pi$ followed by $\iota$ is the endomorphism of $\ker(n\cdot\mathrm{id}_{\mathcal G})$ induced by $\rho_s$, and on sections over any $U$ the point of $A$ attached by $e_U$ to $\iota(x)$ is the canonical morphism $U\to\operatorname{Spec}\Gamma(U,\mathcal O_U)$ followed by $\mathrm{ePts}_{\Gamma(U,\mathcal O_U)}$ of $x$ and then by $i$.
--
--   This identifies the fppf sheaf attached to the Hopf algebra $H$ of the fixed-point subgroup scheme $E$ of an idempotent of $A[k]$ as a direct summand of the $n$-torsion subsheaf $\mathcal G[n]$, the projector being the one induced by $\rho_s$, with the splitting described explicitly on sections through the closed immersion $E\hookrightarrow A$. It is the general form of the statement applied in [`ModularCurve.JZeroNeronIdentityComponent.exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector`](thm.html#ModularCurve.JZeroNeronIdentityComponent.exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector), where the idempotent comes from an Eisenstein projector on the Jacobian of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of ℤ)} (G : RelativeGroupLaw ℤ f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x)
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = G.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : specInt.Fppf} (g : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map g.op s) = GoodReductionJacobian.schemeHomOverComp g.left (MorphismProperty.Over.w g) (e V s))
    (k : ℕ) (n : ℤ) (hkn : (k : ℤ) = n)

    (ρs : 𝒢 ⟶ 𝒢) (φ : SchemeHomOver f f)
    (hφ_sec : ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e U (ρs.1.app (op U) s)).1 = (e U s).1 ≫ φ.1)
    (eKm : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f) (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f))
    (heKm_idem : eKm.1 ≫ eKm.1 = eKm.1)
    (heφ : eKm.1 ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φ.1)
    (heKm_hom : ∀ (LK : RelativeGroupLaw ℤ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
      (∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f) f) =
          G.mul s (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩)) →
      ∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) eKm =
          LK.mul s (NeronModelInfra.schemeHomOverComp x eKm) (NeronModelInfra.schemeHomOverComp y eKm))

    (E : Scheme.{0}) (gX : E ⟶ (Spec (CommRingCat.of ℤ))) (i : E ⟶ A) (j : E ⟶ G.schemeKer k)
    (LE : RelativeGroupLaw ℤ gX)
    (hi : i ≫ f = gX) [IsClosedImmersion i] (hj : j ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = i) [IsClosedImmersion j]
    [IsAffineHom gX] [Flat gX] [LocallyOfFiniteType gX]
    (hfix : ∀ (hj' : j ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f = gX) {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x : SchemeHomOver s (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
      NeronModelInfra.schemeHomOverComp x eKm = x ↔
        ∃ y : SchemeHomOver s gX, NeronModelInfra.schemeHomOverComp y (⟨j, hj'⟩ : SchemeHomOver gX (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)) = x)
    (hcommE : ∀ {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t gX), LE.mul t x y = LE.mul t y x)
    (hi_hom : ∀ (hi' : i ≫ f = gX) {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t gX),
      NeronModelInfra.schemeHomOverComp (LE.mul t x y) (⟨i, hi'⟩ : SchemeHomOver gX f) =
        G.mul t (NeronModelInfra.schemeHomOverComp x ⟨i, hi'⟩) (NeronModelInfra.schemeHomOverComp y ⟨i, hi'⟩))
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) gX)
    (hePts_mul : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H →ₐ[ℤ] T)),
      ePts T (φ * ψ) = LE.mul _ (ePts T φ) (ePts T ψ))
    (hePts_nat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
        (σ : T →ₐ[ℤ] T') (φ : WithConv (H →ₐ[ℤ] T)),
      (ePts T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts T φ).1)
    (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (sE : ∀ U : specInt.Fppf, 𝒥.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (hsE : ∀ {U V : specInt.Fppf} (g : U ⟶ V) (s : 𝒥.1.obj (op V)) (h : H),
      (Additive.toMul (sE U (𝒥.1.map g.op s))) h = (Scheme.Γ.map g.left.op) ((Additive.toMul (sE V s)) h)) :
    ∃ (ι : 𝒥 ⟶ kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))) (π : kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢)) ⟶ 𝒥)
      (w : (n • 𝟙 𝒢) ≫ ρs = ρs ≫ (n • 𝟙 𝒢)),
      ι ≫ π = 𝟙 𝒥 ∧
      π ≫ ι = kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w ∧
      (∀ (U : specInt.Fppf) (x : 𝒥.1.obj (op U)),
        (e U ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) (ι.1.app (op U) x))).1 =
          U.left.toSpecΓ ≫ (ePts Γ(U.left, ⊤) (Additive.toMul (sE U x))).1 ≫ i) := by sorry
