-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/c53d0d5b-555c-52fe-a0f6-062b7c836908
-- title:
--   Sections of G[n] as points of the kernel scheme
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme, $f\colon A\to\operatorname{Spec}R$ a morphism, and $G$ a relative group law on $f$: a functorial group structure on the sets $\{\varphi\colon T\to A \mid \varphi\circ f=t\}$ of points over arbitrary $t\colon T\to\operatorname{Spec}R$, natural under precomposition. Assume $G$ is commutative. Let $\mathcal G$ be a sheaf of abelian groups on the small fppf site of $\operatorname{Spec}R$, whose objects are morphisms $U\to\operatorname{Spec}R$ that are flat and locally of finite presentation, and let $e$ be a family of bijections $\mathcal G(U)\simeq\{\varphi\colon U\to A\mid \varphi\circ f=U\to\operatorname{Spec}R\}$ carrying addition to $G$'s multiplication and commuting with restriction along morphisms of the site. Let $k\in\mathbb N$ and $n\in\mathbb Z$ with $n=k$. Write $A[k]$ for the pullback of the multiplication-by-$k$ endomorphism $G.\mathtt{schemeNsmul}\,k$ of $A$ (the $k$-fold $G$-multiple of the identity point) along the unit section $\operatorname{Spec}R\to A$, with structure morphism $\mathrm{pr}_1$ followed by $f$. Then there exist a relative group law $LK$ on $A[k]$ and bijections $eK$ between the sections over each fppf $U$ of the kernel of $n\cdot 1_{\mathcal G}$ and the $U$-points of $A[k]$, such that: $LK$ is commutative; $\mathrm{pr}_1$ carries $LK$-products to $G$-products and is injective on $T$-points for every $t\colon T\to\operatorname{Spec}R$; each $eK$ is additive for $LK$ and compatible with restriction; and composing $eK(s)$ with $\mathrm{pr}_1$ equals $e$ applied to the image of $s$ under the kernel inclusion.
--
--   This identifies the $n$-torsion subsheaf of an fppf points sheaf with the points functor of the kernel group scheme $A[k]$, kernels of abelian sheaves being computed section by section and a $k$-torsion point factoring uniquely through $A[k]$. It is used in the construction of a retract of the $n$-torsion of the points sheaf attached to an idempotent, on the sheaf side of the comparison for torsion of Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
    (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he_add : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = G.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (k : ℕ) (n : ℤ) (hkn : (k : ℤ) = n) :
    ∃ (LK : RelativeGroupLaw R (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f))
      (eK : ∀ U : (Spec (CommRingCat.of R)).Fppf,
        (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U) ≃ SchemeHomOver U.hom (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),

      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
        LK.mul t x y = LK.mul t y x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
        NeronModelInfra.schemeHomOverComp (LK.mul t x y) (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) =
          G.mul t (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        Function.Injective (fun y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) =>
          NeronModelInfra.schemeHomOverComp y (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f))) ∧

      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
        eK U (s + s') = LK.mul U.hom (eK U s) (eK U s')) ∧
      (∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op V)),
        eK U ((kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.map k.op s) =
          schemeHomOverComp k.left (MorphismProperty.Over.w k) (eK V s)) ∧
      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
        NeronModelInfra.schemeHomOverComp (eK U s) (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) =
          e U ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) s)) := by sorry
