-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_pullback_action_slice_mono_and_equivalence_of_preimage_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.pullback_action_slice_mono_and_equivalence_of_preimage_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/931b3df7-da1f-57d7-969e-ba7ffe4c1386
-- title:
--   Joint monomorphy and equivalence for the slice relation over a saturated open
-- statement:
--   Let $k$ be an algebraically closed field and $f : G \to \operatorname{Spec} k$ a separated, quasi-compact morphism that is smooth of relative dimension $g$, equipped with a relative group law $L$: a group structure, natural in $T$, on the sets of $T$-points $\{\varphi : T \to G \mid \varphi \circ f = t\}$ for each $t : T \to \operatorname{Spec} k$. Let $i : N \to G$ be a closed immersion with $i \circ f$ smooth of relative dimension $h$ and carrying a relative group law $L_N$, and assume $i$ is a homomorphism: $i \circ (x \cdot_{L_N} y) = (i \circ x) \cdot_L (i \circ y)$ for all $T$-points $x, y$ of $N$ over any $t$. Let $S$ be a nonempty affine scheme and $j : S \to G$ with $j \circ f$ locally of finite type. Write $a : N \times_k S \to G$ for the morphism obtained from the base change of $\mathrm{id}_N \times j$ followed by `L.action i`, i.e. $(n, s) \mapsto i(n) \cdot j(s)$, and assume $a$ is étale. Form $R = (N \times_k S) \times_{a, G, j} S$ with $p_1 : R \to N \times_k S \to S$ the first projection followed by the $S$-component, and $p_2 : R \to S$ the second projection. Let $V$ be an open of $S$ with $p_1^{-1}(V) = p_2^{-1}(V)$. Then: (1) for every scheme $T$, two morphisms $x, y : T \to p_1^{-1}(V)$ agreeing after composition with the restriction $p_1 \mid_V : p_1^{-1}(V) \to V$ and after composition with the isomorphism $p_1^{-1}(V) \cong p_2^{-1}(V)$ induced by the equality of opens followed by $p_2 \mid_V$ are equal; and (2) for every scheme $T$, the relation on morphisms $T \to V$ defined by $x \sim y$ if and only if there exists $\varphi : T \to p_1^{-1}(V)$ with $\varphi$ followed by $p_1 \mid_V$ equal to $x$ and $\varphi$ followed by the above isomorphism and $p_2 \mid_V$ equal to $y$, is an equivalence relation.
--
--   This says that, over an open $V$ saturated for the two projections, the orbit relation cut out on the slice $S$ by the action of the closed subgroup $N$ is a jointly monomorphic pair $p_1^{-1}(V) \rightrightarrows V$ whose induced relation on $T$-points is an equivalence relation, i.e. a set-theoretic equivalence relation in the scheme-theoretic sense. It is used in the construction of saturated opens with finite locally free slice relation, a step in the quotient construction for the good-reduction Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_pullback_action_slice_mono_and_equivalence_of_preimage_eq.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.pullback_action_slice_mono_and_equivalence_of_preimage_eq
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
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))
    (V : S.Opens)
    (hV : (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V = (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ⁻¹ᵁ V) :
    (∀ {T : Scheme.{u}} (x y : T ⟶ ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V).toScheme),
        x ≫ ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) = y ≫ ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) → x ≫ (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) = y ≫ (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) → x = y) ∧
      (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ V.toScheme =>
        ∃ φ : T ⟶ ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V).toScheme, φ ≫ ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) = x ∧ φ ≫ (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) = y) := by sorry
