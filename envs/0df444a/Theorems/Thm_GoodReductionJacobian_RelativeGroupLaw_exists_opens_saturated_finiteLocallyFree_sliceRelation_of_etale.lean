-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/e7f61142-dc26-5e1b-9963-8d5558641949
-- title:
--   Finite flat orbit relation on a saturated open of an étale slice
-- statement:
--   The data are: an algebraically closed field $k$; a scheme $G$ with a morphism $f : G \to \operatorname{Spec} k$ that is separated, quasi-compact and smooth of relative dimension $g$; a relative group law $L$ for $f$, that is, a structure `RelativeGroupLaw` assigning to each scheme $T$ and each $t : T \to \operatorname{Spec} k$ a multiplication, a unit and an inversion on the set of pairs $(\varphi : T \to G,\ \varphi \circ f = t)$, subject to associativity, the two unit laws, left inverses, and naturality under precomposition with morphisms $\psi : T' \to T$ over $\operatorname{Spec} k$; a closed immersion $i : N \to G$, a relative group law $L_N$ for the composite $i$ followed by $f$, and smoothness of relative dimension $h$ for that composite; the hypothesis `hi`, which says that for all $T$, all $t : T \to \operatorname{Spec} k$ and all points $x, y$ of $N$ over $t$, composing $L_N.\mathrm{mul}\,t\,x\,y$ with $i$ gives $L.\mathrm{mul}$ of the composites of $x$ and of $y$ with $i$ (so $i$ is a homomorphism on points); and a non-empty affine scheme $S$ together with $j : S \to G$ such that $j$ followed by $f$ is locally of finite type.
--
--   Write $a$ for the morphism $N \times_k S \to G$ obtained as the pullback map $\mathrm{pullback}(i \circ f,\, j \circ f) \to \mathrm{pullback}(i \circ f,\, f)$ induced by $(\mathbb{1}_N, j, \mathbb{1})$, followed by `L.action i`, the morphism $\mathrm{pullback}(i \circ f, f) \to G$ defined as the underlying map of $L.\mathrm{mul}$ applied to the two canonical points $\mathrm{pr}_1$ followed by $i$, and $\mathrm{pr}_2$. The final hypothesis `hEt` is that $a$ is étale. Put $R := \mathrm{pullback}(a, j)$, and let
--   $$p_1 := \mathrm{pullback.fst}(a,j) \text{ followed by } \mathrm{pullback.snd}(i \circ f, j \circ f), \qquad p_2 := \mathrm{pullback.snd}(a,j),$$
--   both morphisms $R \to S$.
--
--   The assertion is the existence of an open subscheme $V$ of $S$ and of a proof `hV` of the saturation identity $p_1^{-1}(V) = p_2^{-1}(V)$ (equality of opens of $R$) for which the following eight conjuncts hold. Throughout, $p_1 \mid_V$ denotes the restriction $p_1^{-1}(V) \to V$ of $p_1$, and $q$ denotes the morphism $p_1^{-1}(V) \to V$ obtained by composing the isomorphism $p_1^{-1}(V) \cong p_2^{-1}(V)$ coming from `hV` with the restriction $p_2 \mid_V : p_2^{-1}(V) \to V$.
--
--   (i) $V$ is non-empty as a scheme.
--
--   (ii)–(iv) $p_1 \mid_V$ is finite, flat and locally of finite presentation.
--
--   (v)–(vii) $q$ is finite, flat and locally of finite presentation.
--
--   (viii) The pair $(p_1\mid_V, q)$ is jointly monomorphic: for every scheme $T$ and all $x, y : T \to p_1^{-1}(V)$, if $x$ followed by $p_1\mid_V$ equals $y$ followed by $p_1\mid_V$, and $x$ followed by $q$ equals $y$ followed by $q$, then $x = y$.
--
--   (ix) For every scheme $T$, the relation on $T$-points of $V$ given by: $x \sim y$ if and only if there is $\varphi : T \to p_1^{-1}(V)$ with $\varphi$ followed by $p_1\mid_V$ equal to $x$ and $\varphi$ followed by $q$ equal to $y$, is an equivalence relation (reflexive, symmetric and transitive, in the sense of `Equivalence`).
--
--   (x) Every point $x$ of $V$ admits an open $U \subseteq V$ with `IsAffineOpen U` such that for every point $r$ of $p_1^{-1}(V)$ whose image under the underlying map of $p_1\mid_V$ is $x$, the image of $r$ under the underlying map of $q$ lies in $U$; that is, the whole class of $x$ for the above relation on points is contained in one affine open of $V$.
--
--   This packages the orbit relation cut out on an étale slice $j : S \to G$ by the action of the closed subgroup $N$ as a finite, flat, locally of finite presentation equivalence relation over a non-empty open $V \subseteq S$ saturated for the two projections, together with the local affineness of the classes. The conjuncts are exactly the hypotheses needed to form an fppf quotient of $V$ by the relation, and the statement is used for that purpose in the construction of the quotient $G/N$ in the good-reduction study of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_finiteLocallyFree_sliceRelation_of_etale
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
    ∃ (V : S.Opens) (hV : (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V = (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ⁻¹ᵁ V),
      Nonempty (V.toScheme) ∧
      IsFinite ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ∧ Flat ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ∧ LocallyOfFinitePresentation ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ∧
      IsFinite (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) ∧ Flat (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) ∧ LocallyOfFinitePresentation (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) ∧
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
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) = y) ∧
      (∀ x : V.toScheme, ∃ U : (V.toScheme).Opens, IsAffineOpen U ∧
        ∀ r : ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V).toScheme, ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V).base r = x → (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)).base r ∈ U) := by sorry
