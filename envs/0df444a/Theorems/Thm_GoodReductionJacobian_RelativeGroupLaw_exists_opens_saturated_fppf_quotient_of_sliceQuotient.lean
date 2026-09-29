-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_fppf_quotient_of_sliceQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/3e8460da-582c-540d-a896-2366fc5eb7f9
-- title:
--   From étale slice quotient to fppf quotient of saturated open
-- statement:
--   Let $k$ be an algebraically closed field, and let $f : G \to \operatorname{Spec} k$ be separated, quasi-compact and smooth of relative dimension $g$, carrying a relative group law $L$, i.e. a group structure on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of points over $k$, natural in $t : T \to \operatorname{Spec} k$. Let $i : N \to G$ be a closed immersion such that $i$ followed by $f$ is smooth of relative dimension $h$ and carries a relative group law $LN$, and assume $i$ is multiplicative: for all $t$ and all points $x,y$ of $N$ over $t$, the $LN$-product of $x$ and $y$ followed by $i$ equals the $L$-product of $x$ followed by $i$ and $y$ followed by $i$. Write $a :=$ `L.action i` $: N\times_k G \to G$ for the $L$-product of the first projection followed by $i$ with the second projection. Let $S$ be affine with $j : S \to G$ locally of finite type over $k$, and assume the base change $a_S : N\times_k S \to G$ of $a$ along $j$ (identity on $N$) is étale. Let $R := (N\times_k S)\times_{a_S,\,G,\,j} S$, with $r_1$ the first projection followed by the projection $N\times_k S \to S$ and $r_2$ the second projection, and let $V \subseteq S$ be a non-empty open with $r_1^{-1}V = r_2^{-1}V$. Suppose given $\pi : V \to Y$ which is finite, flat, locally of finite presentation and surjective, equalises the restrictions of $r_1$ and $r_2$ to $R|_V$, is a coequaliser of them, and whose square with these two restrictions is a pullback. The conclusion: there is an open $U \subseteq G$, non-empty, saturated in the sense that the preimages of $U$ under the projection $N\times_k G \to G$ and under $a$ coincide, together with a scheme $Y$ and $p : U \to Y$ equalising the two restricted maps $U$-wise, with $p$ flat, locally of finite presentation, quasi-compact and surjective, and with the square formed by the restricted projection, the restricted action and $p$, $p$ a pullback.
--
--   This is the step passing from a quotient of the finite flat equivalence relation cut out on an étale slice to an effective fppf quotient of the open subscheme of $G$ swept out by the $N$-action, in the construction of the quotient of $G$ by the subgroup $N$. Unlike the hypothesis on $\pi$, the morphism $p$ produced is not asserted to be finite or to be a coequaliser in schemes, only to be a flat, locally finitely presented, quasi-compact, surjective map whose relation square is a pullback; it is used by [`GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_fppf_quotient_of_isClosedImmersion_of_isAlgClosed`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_fppf_quotient_of_isClosedImmersion_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_saturated_fppf_quotient_of_sliceQuotient
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))
    (V : S.Opens) (hV : (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ V = (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ⁻¹ᵁ V) [Nonempty (V.toScheme)]
    {Y : Scheme.{u}} (π : V.toScheme ⟶ Y) (w : ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) ≫ π = (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) ≫ π)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] [Surjective π]
    (hRπ : IsPullback ((CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∣_ V) (((CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j).isoOfEq hV).hom ≫ ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ V)) π π) (hcoeq : IsColimit (Cofork.ofπ π w)) :
    ∃ (U : G.Opens) (hU : CategoryTheory.Limits.pullback.snd (i ≫ f) f ⁻¹ᵁ U = L.action i ⁻¹ᵁ U),
      Nonempty (U.toScheme) ∧
      ∃ (Y : Scheme.{u}) (p : (U).toScheme ⟶ Y),
        (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U) ≫ p =
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) ≫ p ∧
        Flat p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ Surjective p ∧
        IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f ∣_ U)
          (((CategoryTheory.Limits.pullback (i ≫ f) f).isoOfEq hU).hom ≫ (L.action i ∣_ U)) p p := by sorry
