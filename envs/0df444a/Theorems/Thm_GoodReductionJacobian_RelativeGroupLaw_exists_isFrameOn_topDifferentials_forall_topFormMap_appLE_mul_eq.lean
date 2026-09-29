-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/9ca642a2-0370-5a4a-9fc3-c6b917f0befd
-- title:
--   Left-invariant global frame on the top differentials of G/K
-- statement:
--   Let $K$ be a field, $G$ a scheme and $g\colon G\to\operatorname{Spec}K$ a smooth morphism, smooth of relative dimension $d$, and let `LG` be a relative group law on $g$, i.e. functorial multiplication, unit and inverse operations on the sets $\{\varphi\colon T\to G \mid \varphi\circ g_T = t\}$ of $T$-points over $\operatorname{Spec}K$, satisfying associativity, unit and inverse laws and compatible with base change along $T'\to T$. Then there is a global section $\omega$ of $g$'s $d$-th determinant module `g.topDifferentials d` (the sheafified $d$-th exterior power of the relative Kähler module of $g$) which is a frame on the whole of $G$: for every open $W$ the map $c\mapsto c\cdot(\omega|_W)$ from $\Gamma(G,W)$ to the sections of `g.topDifferentials d` over $W$ is bijective; and which satisfies the following chart-level invariance. Write $p_1,p_2$ for the two projections of $G\times_K G$ and $m$ for the underlying morphism of the product of the two tautological $G\times_K G$-points $\langle p_1\rangle$ and $\langle p_2\rangle$ under `LG.mul` over the base morphism $p_1$ followed by $g$. Let $V,U',U''$ be affine opens of $G$ and $W$ an affine open of $G\times_K G$ with $W\le p_1^{-1}V$, $W\le p_2^{-1}U'$ and $W\le m^{-1}U''$. Equip $\Gamma(G,V),\Gamma(G,U'),\Gamma(G,U'')$ and $\Gamma(G\times_K G,W)$ with the $K$-algebra structures coming from the structure morphisms, and $\Gamma(G\times_K G,W)$ with the algebra structures over $\Gamma(G,V)$, $\Gamma(G,U')$, $\Gamma(G,U'')$ given by the restricted comorphisms of $p_1$, $p_2$, $m$ respectively, assuming each of these three is a scalar tower over $K$. Then for all $\omega'\in\bigwedge^d_{\Gamma(G,U')}\Omega_{\Gamma(G,U')/K}$ and $\omega''\in\bigwedge^d_{\Gamma(G,U'')}\Omega_{\Gamma(G,U'')/K}$ whose images under `g.topToSections d` are the restrictions of $\omega$ to $U'$ and to $U''$, the base-change maps `TopFormOrder.topFormMap` carry $\omega''$ along $m$ and $\omega'$ along $p_2$ to the same element of $\bigwedge^d_{\Gamma(G\times_K G,W)}\Omega_{\Gamma(G\times_K G,W)/\Gamma(G,V)}$.
--
--   This is the existence of a nowhere-vanishing left-invariant global $d$-form on a smooth group scheme over a field, the invariance being expressed universally on affine charts of $G\times_K G$, with the first projection playing the role of the parameter (so that relative forms over $\Gamma(G,V)$ annihilate the directions of the translating point). It feeds the chart-free formulation [`GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq), used in the comparison of invariant differentials on a Néron model with those on its generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq
    {K : Type u} [Field K] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of K))
    [Smooth g] (LG : RelativeGroupLaw K g) (d : ℕ) [SmoothOfRelativeDimension d g] :
    ∃ ω : Γ(g.topDifferentials d, ⊤), Scheme.Modules.IsFrameOn ω ⊤ ∧
      ∀ (V U' U'' : G.Opens) (hV : IsAffineOpen V) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
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
            TopFormOrder.topFormMap K Γ(G, V) Γ(G, U') Γ(pullback g g, W) d ω' := by sorry
