-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_eq_of_iSup_eq_top
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_forall_mul_eq_of_iSup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/b32136e4-99e3-51e1-8670-f57dcf1e8ce9
-- title:
--   Gluing relative group laws along an open cover of the base
-- statement:
--   Let $R$ be a commutative ring, let $A$ be a scheme and $f : A \to \operatorname{Spec} R$ a morphism, let $\iota$ be an index type and let $(U_i)_{i \in \iota}$ be a family of open subsets of $\operatorname{Spec} R$ with $\bigsqcup_i U_i = \top$. For each $i$ suppose given a relative group law $L_i$ on the open subscheme $f^{-1}(U_i)$ regarded as a scheme over $\operatorname{Spec} R$ via the open immersion followed by $f$; here a relative group law on a morphism $g : X \to \operatorname{Spec} R$ is a group structure (multiplication, unit, inverse, with associativity, unit laws and left inverse) on the sets $\{\varphi : T \to X \mid \varphi \circ g' = g'\}$ — for Lean, $\{\varphi \mid \varphi \,\text{followed by}\, g = t\}$ — of $T$-points over each $t : T \to \operatorname{Spec} R$, compatible with precomposition by morphisms $\psi : T' \to T$ over $\operatorname{Spec} R$. Assume the laws agree on overlaps: for all $i, j$, every $t : T \to \operatorname{Spec} R$ and all $T$-points $x, y$ of $f^{-1}(U_i \cap U_j)$ over $t$, the $L_i$-product of the images of $x, y$ in $f^{-1}(U_i)$ and the $L_j$-product of their images in $f^{-1}(U_j)$ have the same composite with the inclusion into $A$. The conclusion is that there is a relative group law $G$ on $f$ itself such that for each $i$, each $t : T \to \operatorname{Spec} R$ and all $T$-points $x, y$ of $f^{-1}(U_i)$ over $t$, the $G$-product of the images of $x$ and $y$ in $A$ equals the $L_i$-product of $x$ and $y$ followed by the inclusion $f^{-1}(U_i) \hookrightarrow A$. Note that each $L_i$ is required to be a group law on $f^{-1}(U_i)$ as a scheme over the whole of $\operatorname{Spec} R$, rather than over $U_i$, so the hypothesis is stronger (and the statement correspondingly weaker) than the usual Zariski-local gluing of group laws over the charts $U_i$.
--
--   This is the Zariski descent statement for group structures on the functor of points: local group laws on the preimages of an open cover of the base that agree on overlaps come from a single relative group law on $A/R$. It is used in the construction of the group structure on a polarised abelian scheme from local data, via [`AlgebraicGeometry.PolarisedAbelianScheme.exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le_of_rigidified`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le_of_rigidified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_eq_of_iSup_eq_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_forall_mul_eq_of_iSup_eq_top
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    {ι : Type u} (U : ι → (Spec (CommRingCat.of R)).Opens) (hU : ⨆ i, U i = ⊤)
    (L : ∀ i, RelativeGroupLaw R ((f ⁻¹ᵁ U i).ι ≫ f))
    (hagree : ∀ (i j : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t ((f ⁻¹ᵁ (U i ⊓ U j)).ι ≫ f)),
      ((L i).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U i).ι =
      ((L j).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U j).ι) :
    ∃ G : RelativeGroupLaw R f, ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t ((f ⁻¹ᵁ U i).ι ≫ f)),
      (G.mul t ⟨x.1 ≫ (f ⁻¹ᵁ U i).ι, by rw [Category.assoc]; exact x.2⟩
        ⟨y.1 ≫ (f ⁻¹ᵁ U i).ι, by rw [Category.assoc]; exact y.2⟩).1 =
      ((L i).mul t x y).1 ≫ (f ⁻¹ᵁ U i).ι := by sorry
