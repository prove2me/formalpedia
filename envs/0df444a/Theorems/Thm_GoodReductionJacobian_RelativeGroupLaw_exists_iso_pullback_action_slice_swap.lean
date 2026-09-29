-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_action_slice_swap
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_iso_pullback_action_slice_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/8225dcf7-fe1b-50aa-bef1-a5c584101ad8
-- title:
--   Symmetry of the slice orbit relation
-- statement:
--   Let $k$ be an algebraically closed field, $G$ a scheme and $f : G \to \operatorname{Spec} k$ a separated, quasi-compact morphism which is smooth of some relative dimension $g$, and let $L$ be a `RelativeGroupLaw` for $f$: a group structure on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} k$, natural in $T$. Let $i : N \to G$ be a closed immersion, $L_N$ a relative group law for $i \circ f$ (smooth of relative dimension $h$), and assume `hi`: for every $t : T \to \operatorname{Spec} k$ and all $T$-points $x, y$ of $N$ over $t$, composing $L_N$-multiplication with $i$ agrees with $L$-multiplication of the composites, i.e. $i$ is a homomorphism on points. Let $S$ be a nonempty affine scheme with $j : S \to G$ such that $j \circ f$ is locally of finite type, and write $a$ for the composite of $\mathrm{id}_N \times j : N \times_k S \to N \times_k G$ with `L.action i`, the morphism given on points by $(n, x) \mapsto i(n) \cdot x$; assume $a$ is étale. Then on $R := (N \times_k S) \times_{a,\,G,\,j} S$ there is a self-isomorphism $\sigma$ interchanging the two maps to $S$, namely $p_1 = \mathrm{pr}_1$ followed by the projection $N \times_k S \to S$, and $p_2 = \mathrm{pr}_2$: one has $p_2 \circ \sigma = p_1$ and $p_1 \circ \sigma = p_2$.
--
--   This records that the orbit relation cut out on a slice $j : S \to G$ by the action of a closed subgroup $N$ is a symmetric relation, the inverse of $N$ supplying the swap of the two projections. It is used in the study of that relation on a slice, in particular in the statements asserting finiteness, flatness and local freeness of the relation scheme over $S$ and the existence of saturated open subschemes on which it is finite locally free.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_action_slice_swap.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_iso_pullback_action_slice_swap
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)) :
    ∃ σ : CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≅
        CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j,
      σ.hom ≫ CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j =
        (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∧
      σ.hom ≫ (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) =
        CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j := by sorry
