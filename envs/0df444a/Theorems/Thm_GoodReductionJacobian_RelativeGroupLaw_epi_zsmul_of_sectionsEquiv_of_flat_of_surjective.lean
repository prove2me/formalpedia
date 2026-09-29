-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_epi_zsmul_of_sectionsEquiv_of_flat_of_surjective
-- name    : GoodReductionJacobian.RelativeGroupLaw.epi_zsmul_of_sectionsEquiv_of_flat_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/ee2409b5-0e87-5c41-aefb-479144bc367e
-- title:
--   Multiplication by n is epi on the fppf points sheaf
-- statement:
--   Let $R$ be a commutative ring and let $f \colon A \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$ equipped with a `RelativeGroupLaw` $G$, i.e. a functorial group structure on the sets $\{\varphi \colon T \to A \mid \varphi \circ\text{-}\,\}$, precisely on $\{\varphi : T \to A \text{ with } f \circ \varphi = t\}$ for each $t \colon T \to \operatorname{Spec} R$, with unit, inverse, associativity and compatibility with precomposition in $T$. Let $\mathcal G$ be a sheaf of abelian groups for the small fppf topology on $\operatorname{Spec} R$, whose site has as objects the morphisms $U \to \operatorname{Spec} R$ that are flat and locally of finite presentation. Assume given, for each such object $U$, a bijection $e_U$ from $\mathcal G(U)$ to the set of morphisms $U \to A$ over $\operatorname{Spec} R$, such that for every morphism $k \colon U \to V$ of the site and every $s \in \mathcal G(V)$ the point $e_U(k^{*}s)$ is $e_V(s)$ precomposed with the underlying morphism of $k$. Let $n$ be a natural number and let $[n] :=$ `G.schemeNsmul n`, the underlying morphism $A \to A$ of the $n$-fold $G$-sum of the identity point of $A$; assume that for every $U$ and every $s \in \mathcal G(U)$ the point $e_U\bigl((n \cdot \mathrm{id}_{\mathcal G})(s)\bigr)$ is $e_U(s)$ followed by $[n]$. If $[n]$ is flat, surjective and locally of finite presentation, then $n \cdot \mathrm{id}_{\mathcal G} \colon \mathcal G \to \mathcal G$ (the integer multiple $(n : \mathbb Z) \cdot \mathbb 1_{\mathcal G}$) is an epimorphism of fppf sheaves of abelian groups.
--
--   This supplies the surjectivity hypothesis needed to form the fppf Kummer sequence $0 \to \mathcal G[n] \to \mathcal G \to \mathcal G \to 0$ for the points sheaf of a relative group scheme, the flatness and finite presentation of $[n]$ being the standard substitutes for smoothness over the étale site. It is used in the construction of $n$-torsion points of the Néron model of the Jacobian of a modular curve, via [`ModularCurve.JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding`](thm.html#ModularCurve.JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding) and [`ModularCurve.nonempty_jZeroNeronPrimaryTorsionCore_of_dvd`](thm.html#ModularCurve.nonempty_jZeroNeronPrimaryTorsionCore_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_epi_zsmul_of_sectionsEquiv_of_flat_of_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra
  GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.epi_zsmul_of_sectionsEquiv_of_flat_of_surjective
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
    (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (n : ℕ)
    (hn : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : 𝒢.1.obj (op U)),
        (e U (((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢).1.app (op U) s)).1 = (e U s).1 ≫ G.schemeNsmul n)
    [Flat (G.schemeNsmul n)] [Surjective (G.schemeNsmul n)] [LocallyOfFinitePresentation (G.schemeNsmul n)] :
    Epi ((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢) := by sorry
