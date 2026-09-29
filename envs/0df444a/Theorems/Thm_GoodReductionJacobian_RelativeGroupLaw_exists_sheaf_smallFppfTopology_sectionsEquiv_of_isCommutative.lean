-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/81019670-70e1-58e2-89d7-e0a04be15b1e
-- title:
--   Commutative relative group law gives an abelian fppf points sheaf
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism, and let $G$ be a relative group law for $f$ over $R$: data assigning to every scheme $T$ and every morphism $t \colon T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set $\{\varphi \colon T \to A \mid \varphi \text{ followed by } f = t\}$, subject to associativity, the two unit laws, left inverses, and naturality of the multiplication under precomposition with morphisms $\psi \colon T' \to T$ satisfying $\psi$ followed by $t$ equals $t'$; assume further that $G$ is commutative, i.e. all these multiplications are commutative. The assertion is the existence of a sheaf $\mathcal G$ of abelian groups on the small fppf site of $\operatorname{Spec} R$ — whose objects $U$ are schemes over $\operatorname{Spec} R$ with structure morphism $U.\mathrm{hom}$ flat and locally of finite presentation — together with bijections $e_U \colon \mathcal G(U) \to \{\varphi \colon U \to A \mid \varphi \text{ followed by } f = U.\mathrm{hom}\}$ for all such $U$, satisfying three compatibilities: $e_U(s + s') = G.\mathrm{mul}\,(U.\mathrm{hom})\,(e_U s)\,(e_U s')$; for every morphism $k \colon U \to V$ of the site, $e_U$ of the restriction $\mathcal G(k)(s)$ is $e_V(s)$ precomposed with the underlying morphism of $k$; and for every natural number $n$, the underlying morphism of $e_U$ applied to the value at $U$ of the endomorphism $(n : \mathbb Z) \cdot \mathrm{id}_{\mathcal G}$ on $s$ equals the underlying morphism of $e_U(s)$ followed by $G.\mathrm{schemeNsmul}\,n$, the underlying morphism of the $n$-fold $G$-product of the identity point $\mathrm{id}_A$.
--
--   This is the statement that a commutative group law on the relative points of $f \colon A \to \operatorname{Spec} R$ is represented by a sheaf of abelian groups on the small fppf site of the base, with explicit identifications of addition, restriction and multiplication by $n$. It is used downstream in the analysis of kernels and torsion of Néron models of Jacobians, in particular for the retract of the kernel of multiplication on the points sheaf and for the construction of primary torsion cores attached to $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (hG : G.IsCommutative) :
    ∃ (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
      (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f),
      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : 𝒢.1.obj (op U)),
          e U (s + s') = G.mul U.hom (e U s) (e U s')) ∧
      (∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
          e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s)) ∧
      (∀ (n : ℕ) (U : (Spec (CommRingCat.of R)).Fppf) (s : 𝒢.1.obj (op U)),
          (e U (((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢).1.app (op U) s)).1 = (e U s).1 ≫ G.schemeNsmul n) := by sorry
