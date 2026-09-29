-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/5d2e4987-0fe5-54a4-aae1-230eed0363ce
-- title:
--   From chart-level translation identity to invariance at field-valued points
-- statement:
--   Let $K$ be a field, let $g\colon G\to\operatorname{Spec}K$ be a smooth morphism of schemes, let $LG$ be a relative group law on $g$ (a functorial group structure on the sets $\{\varphi\colon T\to G \mid \varphi\circ g=t\}$ of $T$-points over $K$, natural in the test scheme), let $d\in\mathbb{N}$ with $g$ smooth of relative dimension $d$, and let $\omega$ be a global section of $g.topDifferentials\ d$, the $d$-th determinant of the sheafified relative Kähler module of $g$. Assume the chart-level hypothesis: for all affine opens $V,U',U''\subseteq G$ and every affine open $W\subseteq G\times_K G$ with $W\le p_1^{-1}V$, $W\le p_2^{-1}U'$ and $W\le m^{-1}U''$, where $m$ is the underlying morphism of $LG.mul$ applied to the two projections viewed as $(G\times_KG)$-points of $G$, and giving $\Gamma(G\times_KG,W)$ its $K$-algebra structure together with the algebra structures over $\Gamma(G,V)$, $\Gamma(G,U')$, $\Gamma(G,U'')$ induced by the restricted comorphisms of $p_1$, $p_2$, $m$, and assuming each of these three towers compatible with $K$, one has: whenever $\omega'\in\bigwedge^d_{\Gamma(G,U')}\Omega_{\Gamma(G,U')/K}$ and $\omega''\in\bigwedge^d_{\Gamma(G,U'')}\Omega_{\Gamma(G,U'')/K}$ both represent $\omega$ (their images under `topToSections` are the restrictions of $\omega$ to $U'$, $U''$), then $\mathrm{topFormMap}\,K\,\Gamma(G,V)\,\Gamma(G,U'')\,\Gamma(W)\,d\ \omega''=\mathrm{topFormMap}\,K\,\Gamma(G,V)\,\Gamma(G,U')\,\Gamma(W)\,d\ \omega'$ in $\bigwedge^d_{\Gamma(W)}\Omega_{\Gamma(W)/\Gamma(G,V)}$. The conclusion is the corresponding statement at field-valued points: for all fields $L,F$ with a compatible tower $K\to L\to F$, every $L$-point $a$ and $F$-point $x$ of $G$ over $K$, and all affine opens $U',U''$ carrying $F$-algebra structures on their sections compatible over $K$ with those coming from $g$, such that $x$ factors through $U'$ by the given map $\Gamma(G,U')\to F$ and the product (in the group law on $F$-points) of the base change of $a$ to $F$ with $x$ factors through $U''$ by the given map $\Gamma(G,U'')\to F$, and for all $\omega',\omega''$ representing $\omega$ on $U'$, $U''$ as above, one has $\mathrm{topFormMap}\,K\,L\,\Gamma(G,U'')\,F\,d\ \omega''=\mathrm{topFormMap}\,K\,L\,\Gamma(G,U')\,F\,d\ \omega'$ in $\bigwedge^d_F\Omega_{F/L}$.
--
--   This is the passage from a universal identity on affine charts of $G\times_K G$, expressing that the pullbacks of a top-degree relative form along multiplication and along the second projection agree, to left invariance of that form evaluated at field-valued points of $G$. It is used in the construction of an invariant frame for the sheaf of top-degree differentials, via [`GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq), in the Néron model infrastructure; the only input cited is the transitivity [`NeronModelInfra.TopFormOrder.topFormMap_topFormMap`](thm.html#NeronModelInfra.TopFormOrder.topFormMap_topFormMap) of the maps on top forms along a tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq
    {K : Type u} [Field K] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of K))
    [Smooth g] (LG : RelativeGroupLaw K g) (d : ℕ) [SmoothOfRelativeDimension d g]
    (ω : Γ(g.topDifferentials d, ⊤))
    (hω : ∀ (V U' U'' : G.Opens) (hV : IsAffineOpen V) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        (W : (pullback g g).Opens) (hW : IsAffineOpen W)
        (hWV : W ≤ pullback.fst g g ⁻¹ᵁ V) (hWU' : W ≤ pullback.snd g g ⁻¹ᵁ U')
        (hWU'' : W ≤ (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
            ⟨pullback.snd g g, pullback.condition.symm⟩).1 ⁻¹ᵁ U''),
        letI := g.sectionsAlgebra V; letI := g.sectionsAlgebra U'; letI := g.sectionsAlgebra U''
        letI := (pullback.fst g g ≫ g).sectionsAlgebra W
        letI : Algebra Γ(G, V) Γ(pullback g g, W) := ((pullback.fst g g).appLE V W hWV).hom.toAlgebra
        letI : Algebra Γ(G, U') Γ(pullback g g, W) := ((pullback.snd g g).appLE U' W hWU').hom.toAlgebra
        letI : Algebra Γ(G, U'') Γ(pullback g g, W) :=
          ((LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
            ⟨pullback.snd g g, pullback.condition.symm⟩).1.appLE U'' W hWU'').hom.toAlgebra
        ∀ [IsScalarTower K Γ(G, V) Γ(pullback g g, W)] [IsScalarTower K Γ(G, U') Γ(pullback g g, W)]
          [IsScalarTower K Γ(G, U'') Γ(pullback g g, W)],
        ∀ (ω' : ⋀[Γ(G, U')]^d (g.kaehlerPresheaf.obj (op U')))
          (ω'' : ⋀[Γ(G, U'')]^d (g.kaehlerPresheaf.obj (op U''))),
          g.topToSections d U' ω' = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          g.topToSections d U'' ω'' = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K Γ(G, V) Γ(G, U'') Γ(pullback g g, W) d ω'' =
            TopFormOrder.topFormMap K Γ(G, V) Γ(G, U') Γ(pullback g g, W) d ω') :
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
