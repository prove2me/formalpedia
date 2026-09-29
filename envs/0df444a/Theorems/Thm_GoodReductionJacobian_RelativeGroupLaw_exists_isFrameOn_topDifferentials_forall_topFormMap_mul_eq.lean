-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/b50f414a-2d90-5ea5-a615-30da554b0a83
-- title:
--   Invariant frame of the top differentials on a smooth group scheme
-- statement:
--   Let $K$ be a field, $G$ a scheme and $g\colon G \to \operatorname{Spec} K$ a smooth morphism which is smooth of relative dimension $d$ for a natural number $d$, and let `LG` be a relative group law on $g$, i.e. a functorial multiplication, unit and inversion on the sets $\{\varphi : T \to G \mid \varphi \circ t = t\}$ of points of $G$ over arbitrary $t\colon T \to \operatorname{Spec} K$, satisfying associativity, the unit laws, left inversion and compatibility with composition by morphisms $T' \to T$. Then there is a global section $\omega$ of `g.topDifferentials d`, the $d$-th determinant (sheafified exterior power) of the relative Kähler module of $g$, with the following two properties. First, $\omega$ is a frame on $\top$: for every open $W \subseteq G$, multiplication by $\omega|_W$ is a bijection from $\Gamma(G, W)$ onto the sections of `g.topDifferentials d` over $W$. Second, for all fields $L$, $F$ forming a tower $K \to L \to F$, every point $a$ of $G$ over $\operatorname{Spec} L \to \operatorname{Spec} K$ and every point $x$ of $G$ over $\operatorname{Spec} F \to \operatorname{Spec} K$, and all affine opens $U', U'' \subseteq G$ equipped with $F$-algebra structures on $\Gamma(G, U')$ and $\Gamma(G, U'')$ compatible, via the algebra structures induced by $g$, with the towers over $K$: if $\operatorname{Spec} F \to \operatorname{Spec}\Gamma(G,U')$ followed by `hU'.fromSpec` is $x$, and the corresponding morphism for $U''$ is the product, under `LG.mul` over $\operatorname{Spec} F$, of the base change of $a$ along $L \to F$ with $x$, then for any $\omega' \in \bigwedge^d_{\Gamma(G,U')} \Omega_{\Gamma(G,U')/K}$ and $\omega'' \in \bigwedge^d_{\Gamma(G,U'')} \Omega_{\Gamma(G,U'')/K}$ whose images under `g.topToSections d` are the restrictions of $\omega$ to $U'$ and to $U''$ respectively, the images of $\omega''$ and $\omega'$ under the base-change maps `TopFormOrder.topFormMap` agree in $\bigwedge^d_F \Omega_{F/L}$.
--
--   This is the existence of a nowhere-vanishing, translation-invariant global $d$-form on a smooth group scheme of relative dimension $d$ over a field, with invariance recorded on field-valued points: the values of $\omega$ at $x$ and at $a \cdot x$ coincide in $\bigwedge^d_F \Omega_{F/L}$. It is used in the construction of Néron models, namely by [`NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative`](thm.html#NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq
    {K : Type u} [Field K] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of K))
    [Smooth g] (LG : RelativeGroupLaw K g) (d : ℕ) [SmoothOfRelativeDimension d g] :
    ∃ ω : Γ(g.topDifferentials d, ⊤), Scheme.Modules.IsFrameOn ω ⊤ ∧
      ∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) g)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) g)
        (U' U'' : G.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(G, U') F] [Algebra Γ(G, U'') F],
        letI := g.sectionsAlgebra U'; letI := g.sectionsAlgebra U''
        ∀ [IsScalarTower K Γ(G, U') F] [IsScalarTower K Γ(G, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(G, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(G, U'') F)) ≫ hU''.fromSpec =
          (LG.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(G, U')]^d (g.kaehlerPresheaf.obj (op U')))
          (ω'' : ⋀[Γ(G, U'')]^d (g.kaehlerPresheaf.obj (op U''))),
          g.topToSections d U' ω' = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          g.topToSections d U'' ω'' = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(G, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(G, U') F d ω' := by sorry
