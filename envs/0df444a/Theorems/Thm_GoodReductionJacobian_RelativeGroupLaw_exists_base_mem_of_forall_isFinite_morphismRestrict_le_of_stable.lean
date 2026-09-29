-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_base_mem_of_forall_isFinite_morphismRestrict_le_of_stable
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_base_mem_of_forall_isFinite_morphismRestrict_le_of_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/2f5862e8-a0c0-5fdb-a459-14cedd682f52
-- title:
--   A point of an étale slice lands in the finite locus
-- statement:
--   Let $k$ be an algebraically closed field, let $f : G \to \operatorname{Spec} k$ be a separated, quasi-compact morphism of schemes which is smooth of relative dimension $g$, and let $L$ be a relative group law on $f$: for every $t : T \to \operatorname{Spec} k$ a group structure (`mul`, `one`, `inv`, with associativity, unit and inverse laws) on the set of $\varphi : T \to G$ with $\varphi \circ f = t$, natural in $T$. Let $i : N \to G$ be a closed immersion such that $i$ followed by $f$ is smooth of relative dimension $h$, equipped with a relative group law $L_N$, and assume $i$ is a homomorphism: for all $t : T \to \operatorname{Spec} k$ and all sections $x, y$ of $i \circ f$ over $t$, post-composing $L_N.\mathrm{mul}\,t\,x\,y$ with $i$ gives $L.\mathrm{mul}$ of the post-composites of $x$ and $y$ with $i$. Let $S$ be a nonempty affine scheme and $j : S \to G$ a morphism with $j$ followed by $f$ locally of finite type. Write $a$ for the action map $N \times_{\operatorname{Spec} k} S \to G$ obtained from the canonical morphism $N \times_{\operatorname{Spec} k} S \to N \times_{\operatorname{Spec} k} G$ induced by $\mathrm{id}_N$ and $j$ followed by $L.\mathrm{action}\,i$, the latter being the underlying morphism of $L.\mathrm{mul}$ applied to the two projections $(n, x) \mapsto i(n) \cdot x$ on $N \times_{\operatorname{Spec} k} G$; assume $a$ is étale. Let $U$ be an open subscheme of $G$ such that (i) every open $W \subseteq G$ over which the restriction $a \mid_W$ is finite satisfies $W \le U$, and (ii) for every $n : \operatorname{Spec} k \to N$ with $n$ followed by $i$ followed by $f$ the identity, the underlying morphism of $L.\mathrm{mul}\,f$ applied to the constant section $f \circ n \circ i$ and to $\mathrm{id}_G$ — translation by $n$ — pulls $U$ back to $U$. Then there exists a point $s$ of $S$ whose image $j(s)$ lies in $U$.
--
--   This is the slice step in the construction of quotients by étale (finite flat) groupoid actions used for Néron models and good reduction of Jacobians: it says that an étale slice $j : S \to G$ meets the open set $U$ determined by the loci of finiteness of the action map and stable under translation by the $k$-points of $N$. It is invoked by [`GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale), and rests on generic finiteness of separated quasi-compact locally quasi-finite morphisms over an irreducible base ([`AlgebraicGeometry.LocallyQuasiFinite.exists_isFinite_morphismRestrict_of_irreducibleSpace`](thm.html#AlgebraicGeometry.LocallyQuasiFinite.exists_isFinite_morphismRestrict_of_irreducibleSpace)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_base_mem_of_forall_isFinite_morphismRestrict_le_of_stable.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_base_mem_of_forall_isFinite_morphismRestrict_le_of_stable
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
    (U : G.Opens) (hU : ∀ W : G.Opens, IsFinite ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ∣_ W) → W ≤ U)
    (hUstab : ∀ (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _),
      (L.mul f ⟨f ≫ n ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 ⁻¹ᵁ U = U) :
    ∃ s : S, j.base s ∈ U := by sorry
