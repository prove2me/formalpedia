-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/6d70e688-f564-5d0f-884d-fc90420bf80a
-- title:
--   Maximal open of finiteness for a translation-stable slice action
-- statement:
--   Let $k$ be an algebraically closed field, let $G$ be a scheme and $f : G \to \operatorname{Spec} k$ a separated, quasi-compact morphism, and let $L$ be a relative group law for $f$ over $k$: a functorial group structure on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of points of $G$ over each $t : T \to \operatorname{Spec} k$, with multiplication, unit, inverse, associativity, two-sided unit law, left inverse law, and compatibility with precomposition in $T$. Assume $f$ is smooth of some relative dimension $g$. Let $i : N \to G$ be a closed immersion, $L_N$ a relative group law for $i$ followed by $f$, with that composite smooth of some relative dimension $h$, and assume $i$ is a homomorphism: for all $T$, all $t : T \to \operatorname{Spec} k$ and all points $x, y$ of $N$ over $t$, the composite of $L_N.\mathrm{mul}\,t\,x\,y$ with $i$ equals $L.\mathrm{mul}$ of the composites of $x$ and $y$ with $i$. Let $S$ be a nonempty affine scheme and $j : S \to G$ a morphism with $j$ followed by $f$ locally of finite type. Write $a$ for the composite of the pullback map $N \times_k S \to N \times_k G$ induced by $(\mathbf{1}_N, j)$ with the action morphism $L.\mathrm{action}\,i : N \times_k G \to G$, $(n,x) \mapsto i(n) \cdot x$, and assume $a$ is étale. Then there is an open subscheme $U$ of $G$ such that the restriction of $a$ over $U$ is finite, every open $W$ over which the restriction of $a$ is finite satisfies $W \le U$, and for every $k$-point $n : \operatorname{Spec} k \to N$ (so $n$ followed by $i$ followed by $f$ is the identity) the preimage of $U$ under the underlying morphism of $L.\mathrm{mul}\,f$ applied to the constant $G$-point $i \circ n$ and the identity $G$-point, i.e. under left translation $x \mapsto i(n) \cdot x$, equals $U$.
--
--   This isolates the largest open subscheme of $G$ over which the étale action map of a slice $S$ under the subgroup scheme $N$ is finite, and records that this locus is invariant under translation by the $k$-points of $N$. It feeds the construction of a finite locally free groupoid relation on a slice, being used in [`GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_isFinite_morphismRestrict_action_slice_maximal_stable
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
    ∃ U : G.Opens,
      IsFinite ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ∣_ U) ∧
      (∀ W : G.Opens, IsFinite ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ∣_ W) → W ≤ U) ∧
      (∀ (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _),
        (L.mul f ⟨f ≫ n ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 ⁻¹ᵁ U = U) := by sorry
