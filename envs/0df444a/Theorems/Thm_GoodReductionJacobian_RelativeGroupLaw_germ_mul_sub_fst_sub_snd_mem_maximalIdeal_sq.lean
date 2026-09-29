-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq
-- name    : GoodReductionJacobian.RelativeGroupLaw.germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/43b59eed-1312-5f8a-8361-1b1ecc42eddd
-- title:
--   Group law is additive to first order at the unit
-- statement:
--   Let $k$ be a field, $G$ a scheme and $f : G \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$: data assigning to every scheme $T$ and every $t : T \to \operatorname{Spec} k$ a multiplication, a unit and an inversion on the set of morphisms $T \to G$ over $t$, subject to associativity, both unit laws, left inverses, and naturality under precomposition with morphisms $\psi : T' \to T$ over $\operatorname{Spec} k$. Write $m : G \times_k G \to G$ for the underlying morphism of the product of the two projections, taken in the group of points of $G \times_k G$ over $\operatorname{pr}_1$ followed by $f$, and $e$ for the image of the closed point of $\operatorname{Spec} k$ under the unit section associated with $\mathrm{id}_{\operatorname{Spec} k}$. Let $U \subseteq G$ and $W \subseteq G \times_k G$ be open, with $W$ contained in the preimages of $U$ under $m$, $\operatorname{pr}_1$ and $\operatorname{pr}_2$, with $e \in U$ and with the point $(e,e)$, the image of the closed point under the morphism induced by the unit section in both factors, lying in $W$. Then for every $\varphi \in \Gamma(G, U)$ whose germ at $e$ lies in the maximal ideal of $\mathcal O_{G,e}$, the germ at $(e,e)$ of $m^{*}\varphi - \operatorname{pr}_1^{*}\varphi - \operatorname{pr}_2^{*}\varphi \in \Gamma(G \times_k G, W)$, the restrictions being those along the three morphisms from $U$ to $W$, lies in the square of the maximal ideal of $\mathcal O_{G \times_k G, (e,e)}$.
--
--   This is the infinitesimal statement that the cotangent map of the multiplication at the unit is the sum of the cotangent maps of the two projections, i.e. that the group law is addition to first order on tangent vectors at the identity. It is used in the good-reduction infrastructure for Jacobians, in the construction of an affine neighbourhood on which the stalk map of the action at the unit is formally unramified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq
    {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (U : G.Opens) (W : (pullback f f).Opens)
    (hWm : W ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ U)
    (hW₁ : W ≤ pullback.fst f f ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd f f ⁻¹ᵁ U)
    (he : (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k) ∈ U)
    (hee : pullback.lift (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (L.one (𝟙 (Spec (CommRingCat.of k)))).1 rfl
      (IsLocalRing.closedPoint k) ∈ W)
    (φ : Γ(G, U)) (hφ : (G.presheaf.germ U _ he).hom φ ∈ IsLocalRing.maximalIdeal (G.presheaf.stalk _)) :
    ((pullback f f).presheaf.germ W _ hee).hom
        (((L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1.appLE U W hWm).hom φ
          - ((pullback.fst f f).appLE U W hW₁).hom φ - ((pullback.snd f f).appLE U W hW₂).hom φ)
      ∈ IsLocalRing.maximalIdeal ((pullback f f).presheaf.stalk _) ^ 2 := by sorry
