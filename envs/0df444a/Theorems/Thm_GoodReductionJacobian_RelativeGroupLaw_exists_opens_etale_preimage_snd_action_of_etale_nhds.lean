-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_etale_preimage_snd_action_of_etale_nhds
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_opens_etale_preimage_snd_action_of_etale_nhds
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/898c92a2-4d71-5f79-a528-55ad682b2f1a
-- title:
--   Étaleness of (n,s)↦ i(n) j'(s) spreads to a tube
-- statement:
--   Let $k$ be an algebraically closed field, let $f : G \to \operatorname{Spec} k$ be locally of finite type, and let `L` be a relative group law on $f$, i.e. a group structure on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of sections over each $k$-scheme $t : T \to \operatorname{Spec} k$, natural in $T$. Let $i : N \to G$ be a closed immersion carrying a relative group law `LN` on $i$ followed by $f$, such that $i$ is a homomorphism: for all $t : T \to \operatorname{Spec} k$ and all sections $x,y$ of $N$ over $t$, composing `LN.mul t x y` with $i$ equals `L.mul t` of the composites of $x$ and $y$ with $i$. Let $j' : S' \to G$ with $j'$ followed by $f$ locally of finite type, and let $e_S : \operatorname{Spec} k \to S'$ be a section of that structure morphism. Write $a'$ for the morphism $N \times_k S' \to G$ obtained from $\mathrm{id}_N \times j'$ followed by `L.action i`, the multiplication $\mathrm{pr}_1 \circ i$ by $\mathrm{pr}_2$ on $N \times_k G$. Assume $W$ is an open of $N \times_k S'$ containing the point $(1_N, e_S)$ (the image of the closed point of $\operatorname{Spec} k$ under the lift of the unit section of `LN` and $e_S$), and that the restriction of $a'$ to $W$ is étale. Then there is an open $S_0 \subseteq S'$ containing the image of the closed point under $e_S$ such that the restriction of $a'$ to $\mathrm{pr}_{S'}^{-1}(S_0) = N \times_k S_0$ is étale.
--
--   This is the homogeneity (translation) argument for relative group laws: the étale locus of the multiplication map $(n,s) \mapsto i(n)\,j'(s)$ is stable under left translation by $k$-points of $N$, so étaleness near the unit slice propagates along the whole tube over an open of $S'$. It is used in the construction of an affine étale slice over an algebraically closed field, [`GoodReductionJacobian.RelativeGroupLaw.exists_affine_etale_slice_of_isAlgClosed`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_affine_etale_slice_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_etale_preimage_snd_action_of_etale_nhds.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_etale_preimage_snd_action_of_etale_nhds
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S' : Scheme.{u}) (j' : S' ⟶ G) [LocallyOfFiniteType (j' ≫ f)]
    (eS : Spec (CommRingCat.of k) ⟶ S') (heS : eS ≫ j' ≫ f = 𝟙 _)
    (W : (pullback (i ≫ f) (j' ≫ f)).Opens)
    (hzW : pullback.lift (LN.one (𝟙 _)).1 eS ((LN.one (𝟙 _)).2.trans heS.symm) (IsLocalRing.closedPoint k) ∈ W)
    (hW : Etale (W.ι ≫ (pullback.map (i ≫ f) (j' ≫ f) (i ≫ f) f (𝟙 N) j' (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))) :
    ∃ S₀ : S'.Opens, eS (IsLocalRing.closedPoint k) ∈ S₀ ∧
      Etale ((pullback.snd (i ≫ f) (j' ≫ f) ⁻¹ᵁ S₀).ι ≫ (pullback.map (i ≫ f) (j' ≫ f) (i ≫ f) f (𝟙 N) j' (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)) := by sorry
