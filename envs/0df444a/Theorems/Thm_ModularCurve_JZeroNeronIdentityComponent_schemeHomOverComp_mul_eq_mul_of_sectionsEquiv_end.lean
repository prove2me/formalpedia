-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_schemeHomOverComp_mul_eq_mul_of_sectionsEquiv_end
-- name    : ModularCurve.JZeroNeronIdentityComponent.schemeHomOverComp_mul_eq_mul_of_sectionsEquiv_end
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/23bb81b1-7720-5819-81a0-c57dcdda201b
-- title:
--   Sheaf endomorphism acting by φ makes φ additive on points
-- statement:
--   Fix a prime $p$ and a datum $N$ of type `JZeroNeronIdentityComponent p`, consisting of a scheme $G = N.G$ over $\operatorname{Spec}\mathbb{Z}$ via $g = N.g$, a relative group law $L = N.L$ on $g$ (functorial multiplication, unit and inverse on the sets $\{\varphi : T \to G \mid \varphi \text{ followed by } g = t\}$ of $T$-points over $t$, satisfying the group axioms and naturality under base change), an identification of `JZero p` with the points over $\overline{\mathbb{Q}}$, and the further smoothness, separatedness, finiteness, surjectivity, fibre and Hecke conditions of that structure. Let $\mathcal{G}$ be an abelian sheaf on the small fppf site of $\operatorname{Spec}\mathbb{Z}$ (objects: schemes $U$ over $\operatorname{Spec}\mathbb{Z}$ whose structure morphism is flat and locally of finite presentation). Assume given bijections $e_U : \mathcal{G}(U) \simeq \{\varphi : U \to G \mid \varphi \text{ followed by } g = U.\mathrm{hom}\}$ which carry addition to $L.\mathrm{mul}$ (`he_add`) and are natural in $U$, sending $\mathcal{G}(k)$ to precomposition with the underlying morphism of $k$ (`he`). Let $F$ be an endomorphism of the abelian sheaf $\mathcal{G}$ and $\varphi : G \to G$ a morphism over $\operatorname{Spec}\mathbb{Z}$ such that, for every $U$ and every section $s$, the point $e_U(F(s))$ is $e_U(s)$ followed by $\varphi$. Then for every scheme $T$ with a morphism $t : T \to \operatorname{Spec}\mathbb{Z}$ and all $T$-points $x, y$ of $G$ over $t$, the point $L.\mathrm{mul}\,t\,x\,y$ followed by $\varphi$ equals $L.\mathrm{mul}\,t$ applied to $x$ followed by $\varphi$ and $y$ followed by $\varphi$.
--
--   This is the statement that a morphism $\varphi$ of the Néron identity component which realises an endomorphism of the associated fppf points sheaf respects the relative group law on arbitrary points, i.e. is a homomorphism in the functor-of-points sense; it is exactly the first conjunct required of the Hecke-induced morphisms in the `JZeroNeronIdentityComponent` structure. It is used in the construction of Hecke-algebra towers and idempotents attached to such a sheaf endomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronIdentityComponent_schemeHomOverComp_mul_eq_mul_of_sectionsEquiv_end.lean

import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.JZeroNeronIdentityComponent.schemeHomOverComp_mul_eq_mul_of_sectionsEquiv_end
    (p : ℕ) [Fact p.Prime] (N : JZeroNeronIdentityComponent p)
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = N.L.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (F : End 𝒢) (φ : SchemeHomOver N.g N.g)
    (hF : ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e U (F.1.app (op U) s)).1 = (e U s).1 ≫ φ.1)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver t N.g) :
    NeronModelInfra.schemeHomOverComp (N.L.mul t x y) φ =
      N.L.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) := by sorry
