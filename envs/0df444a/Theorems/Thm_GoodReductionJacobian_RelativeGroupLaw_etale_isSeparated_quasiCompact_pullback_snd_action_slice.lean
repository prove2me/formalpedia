-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_etale_isSeparated_quasiCompact_pullback_snd_action_slice
-- name    : GoodReductionJacobian.RelativeGroupLaw.etale_isSeparated_quasiCompact_pullback_snd_action_slice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/385b69b6-a518-5b8c-8aac-e083fbd43510
-- title:
--   Étale, separated, quasi-compact target projection of a slice relation
-- statement:
--   Let $k$ be an algebraically closed field and let $f : G \to \operatorname{Spec} k$ be a morphism of schemes that is separated and quasi-compact, equipped with a relative group law $L$ for $f$, that is, a group structure on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of points of $G$ over each $t : T \to \operatorname{Spec} k$, compatible with precomposition in $T$. Assume $f$ is smooth of relative dimension $g$ for some natural number $g$. Let $i : N \to G$ be a closed immersion, let $L_N$ be a relative group law for $i$ followed by $f$, assume the latter morphism smooth of relative dimension $h$, and assume that $i$ is a homomorphism in the sense that for every $t : T \to \operatorname{Spec} k$ and all points $x, y$ of $N$ over $t$, the composite of the $L_N$-product of $x$ and $y$ with $i$ equals the $L$-product of the composites of $x$ and of $y$ with $i$. Let $S$ be an affine nonempty scheme with a morphism $j : S \to G$ such that $j$ followed by $f$ is locally of finite type. Write $a : N \times_{\operatorname{Spec} k} S \to G$ for the morphism obtained by following the pullback map $(\mathbf 1_N, j)$ from $\mathrm{pullback}(i \circ f, j \circ f)$ to $\mathrm{pullback}(i \circ f, f)$ with `L.action i`, the morphism given by the $L$-product of the first projection composed with $i$ and the second projection. Assuming $a$ is étale, the conclusion is that the second projection of the fibre product of $a$ and $j$, a morphism onto $S$, is étale, separated and quasi-compact.
--
--   The morphism in question is the target projection of the orbit relation cut out on a slice $S \subseteq G$ by the action of the closed subgroup $N$; the three properties asserted are the standing hypotheses needed to form quotients by such a relation. It is used in the construction of saturated open slices with finite locally free relation, through [`GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_etale_isSeparated_quasiCompact_pullback_snd_action_slice.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.etale_isSeparated_quasiCompact_pullback_snd_action_slice
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
    Etale (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∧
    IsSeparated (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∧
    QuasiCompact (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) := by sorry
