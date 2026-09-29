-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_of_idempotent
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_of_idempotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/8016b924-d319-56d4-8415-eef60cce12ca
-- title:
--   Idempotent image splits off a retract of G[n]
-- statement:
--   Let $R$ be a commutative ring, $f\colon A\to\operatorname{Spec}R$ a morphism of schemes and $G$ a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi\colon T\to A \mid \varphi\circ f=t\}$ of $T$-points over $\operatorname{Spec}R$. Let $\mathcal G$ be a sheaf of abelian groups on the small fppf site of $\operatorname{Spec}R$ together with bijections $e_U\colon\mathcal G(U)\simeq\{$points of $A$ over $U\}$ carrying addition to `G.mul` and commuting with restriction. Let $k\in\mathbb N$, $n\in\mathbb Z$ with $k=n$, and let $K$ be the pullback of `G.schemeNsmul k` (multiplication by $k$ on $A$) along the identity section of $G$, with structure morphism `pullback.fst` followed by $f$. Assume: a relative group law $LK$ on $K$ for which post-composition with `pullback.fst` is a homomorphism to $G$ and is injective on $T$-points; bijections $e^K_U$ between the sections of $\ker(n\cdot\mathrm{id}_{\mathcal G})$ over $U$ and the points of $K$ over $U$, additive for $LK$ and compatible with restriction; an endomorphism $\rho_s$ of $\mathcal G$ commuting with $n\cdot\mathrm{id}_{\mathcal G}$ (witness $w$); an endomorphism $e_{Km}$ of $K$ over $\operatorname{Spec}R$ that is idempotent and a homomorphism for $LK$, and that induces on sections, through $e^K$, the endomorphism `kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w`. Assume further a scheme $E$ with a closed immersion $i\colon E\to K$, a relative group law $LE$ on $i$ followed by the structure morphism of $K$ for which post-composition with $i$ is a homomorphism to $LK$, the condition that a $T$-point $x$ of $K$ satisfies $x\circ e_{Km}=x$ exactly when $x$ factors through $i$, and a sheaf $\mathcal G_E$ of abelian groups on the same site with bijections $e^E_U$ onto the points of $E$ over $U$, additive for $LE$ and compatible with restriction. Then there exist morphisms of sheaves $\iota\colon\mathcal G_E\to\ker(n\cdot\mathrm{id}_{\mathcal G})$ and $\pi\colon\ker(n\cdot\mathrm{id}_{\mathcal G})\to\mathcal G_E$ with $\pi\circ\iota=\mathrm{id}_{\mathcal G_E}$ and $\iota\circ\pi=$ `kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w`, such that on sections over each $U$ the map $\iota$ is post-composition with $i$ (i.e. $e^K_U(\iota(x))=e^E_U(x)$ followed by $i$) and $\pi$ is given by applying $e_{Km}$ (i.e. $e^E_U(\pi(s))$ followed by $i$ equals $e^K_U(s)$ followed by $e_{Km}$).
--
--   This is the functor-of-points statement that the image of an idempotent endomorphism of the $k$-torsion kernel scheme of a relative group law splits the $n$-torsion subsheaf $\ker(n\cdot\mathrm{id}_{\mathcal G})$ as a retract, the retraction being the endomorphism induced by $\rho_s$. It is used by [`GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent), and ultimately serves to exhibit the part of $\mathcal J^0[q^m]$ cut out by an Eisenstein idempotent as a direct summand.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_of_idempotent.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_of_idempotent
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
    (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he_add : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = G.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (j : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map j.op s) = schemeHomOverComp j.left (MorphismProperty.Over.w j) (e V s))

    (k : ℕ) (n : ℤ) (hkn : (k : ℤ) = n)
    (LK : RelativeGroupLaw R (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f))
    (hLK_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
      NeronModelInfra.schemeHomOverComp (LK.mul t x y) (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) =
        G.mul t (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)
          (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩))
    (hLK_inj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      Function.Injective (fun y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) =>
        NeronModelInfra.schemeHomOverComp y (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f)))
    (eK : ∀ U : (Spec (CommRingCat.of R)).Fppf, (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U) ≃ SchemeHomOver U.hom (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f))
    (heK_add : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
      eK U (s + s') = LK.mul U.hom (eK U s) (eK U s'))
    (heK : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (j : U ⟶ V) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op V)),
      eK U ((kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.map j.op s) = schemeHomOverComp j.left (MorphismProperty.Over.w j) (eK V s))

    (ρs : 𝒢 ⟶ 𝒢) (w : (n • 𝟙 𝒢) ≫ ρs = ρs ≫ (n • 𝟙 𝒢))
    (eKm : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f))
    (heKm_idem : eKm.1 ≫ eKm.1 = eKm.1)
    (heKm_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
      NeronModelInfra.schemeHomOverComp (LK.mul t x y) eKm =
        LK.mul t (NeronModelInfra.schemeHomOverComp x eKm) (NeronModelInfra.schemeHomOverComp y eKm))
    (hρs : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
      eK U ((kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w).1.app (op U) s) = NeronModelInfra.schemeHomOverComp (eK U s) eKm)

    (E : Scheme.{u}) (i : E ⟶ pullback (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1)
    [IsClosedImmersion i]
    (LE : RelativeGroupLaw R (i ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)))
    (hLE_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f))),
      NeronModelInfra.schemeHomOverComp (LE.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)) (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)) =
        LK.mul t (NeronModelInfra.schemeHomOverComp x ⟨i, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩))
    (hfix : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
      NeronModelInfra.schemeHomOverComp x eKm = x ↔
        ∃ y : SchemeHomOver t (i ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)), NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩ = x)
    (𝒢E : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
    (eE : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢E.1.obj (op U) ≃ SchemeHomOver U.hom (i ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)))
    (heE_add : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : 𝒢E.1.obj (op U)), eE U (s + s') = LE.mul U.hom (eE U s) (eE U s'))
    (heE : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (j : U ⟶ V) (s : 𝒢E.1.obj (op V)),
        eE U (𝒢E.1.map j.op s) = schemeHomOverComp j.left (MorphismProperty.Over.w j) (eE V s)) :
    ∃ (ι : 𝒢E ⟶ kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))) (π : kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢)) ⟶ 𝒢E),
      ι ≫ π = 𝟙 𝒢E ∧
      π ≫ ι = kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w ∧
      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (x : 𝒢E.1.obj (op U)),
        eK U (ι.1.app (op U) x) = NeronModelInfra.schemeHomOverComp (eE U x) ⟨i, rfl⟩) ∧
      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
        NeronModelInfra.schemeHomOverComp (eE U (π.1.app (op U) s)) ⟨i, rfl⟩ =
          NeronModelInfra.schemeHomOverComp (eK U s) eKm) := by sorry
