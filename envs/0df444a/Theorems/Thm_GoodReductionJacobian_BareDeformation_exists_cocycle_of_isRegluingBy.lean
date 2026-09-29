-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_cocycle_of_isRegluingBy
-- name    : GoodReductionJacobian.BareDeformation.exists_cocycle_of_isRegluingBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/fe7630e1-ee39-5410-b035-8b3fbe7e67d6
-- title:
--   Cocycle identity for the transitions of a re-gluing
-- statement:
--   Let $B$ and $B_1$ be commutative rings with $B_1$ a $B$-algebra such that the structure map $B \to B_1$ is surjective with nilpotent kernel. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ be a scheme over $B_1$ carrying a relative group law $L_1$, and let $D_0$ be a bare deformation of $(f_1, L_1)$ over $B$: a scheme $D_0.A$ with a structure morphism $D_0.f$ to $\operatorname{Spec} B$, a commutative relative group law, the property bundle asserting smoothness, properness, connected fibres and existence of a relative group law, together with $D_0.g : A_1 \to D_0.A$ making a pullback square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ and compatible with the group laws. Let $\mathcal U$ be an ordered affine cover of $D_0.A$, i.e. a finite linearly ordered index type with affine opens $U_i$ whose supremum is $\top$; for a strictly monotone $(i+1)$-tuple $s$ write $\mathcal U.\mathrm{inter}\,s$ for $\bigcap_j U_{s(j)}$ and $\mathcal U.\mathrm{face}\,s\,j$ for the tuple with the $j$-th entry deleted. Let $\tau$ assign to each $1$-simplex $s$ a self-isomorphism of the open subscheme $\mathcal U.\mathrm{inter}\,s$, and let $D$ be a second bare deformation of $(f_1, L_1)$ over $B$ with $D_0.\mathrm{IsRegluingBy}\ \mathcal U\ \tau\ D$: each $\tau_s$ commutes with the structure morphism to $\operatorname{Spec} B$ and fixes the restriction of $D_0.g$ to $\mathcal U.\mathrm{inter}\,s$, and there are morphisms $\iota_i : U_i \to D.A$ which are open immersions, lie over $D_0.f$, are jointly surjective on points, are compatible with $D_0.g$, and satisfy, on each $1$-simplex $s$, that the inclusion of $\mathcal U.\mathrm{inter}\,s$ into $U_{s(0)}$ followed by $\iota_{s(0)}$ equals $\tau_s$ followed by the inclusion into $U_{s(1)}$ followed by $\iota_{s(1)}$. The conclusion is that for every $2$-simplex $r$ there is a family $\rho : \mathrm{Fin}\,3 \to \operatorname{End}(\mathcal U.\mathrm{inter}\,r)$ such that for each $j$ the composite of $\rho_j$ with the inclusion $\mathcal U.\mathrm{inter}\,r \subseteq \mathcal U.\mathrm{inter}(\mathcal U.\mathrm{face}\,r\,j)$ agrees with that inclusion followed by $\tau_{\mathcal U.\mathrm{face}\,r\,j}$, and $\rho_1 = \rho_0 \circ \rho_2$.
--
--   This is the cocycle (or recollement) condition for the overlap transition isomorphisms of a re-gluing: the transitions $\tau_{ij}$ restrict to endomorphisms of each triple overlap $U_i \cap U_j \cap U_k$ and there satisfy $\tau_{ik} = \tau_{jk} \tau_{ij}$ in the appropriate order. It is the input needed for glueing data over a nilpotent thickening, and is used in the analysis of shifts of bare deformations in terms of tangent coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_cocycle_of_isRegluingBy.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct

theorem GoodReductionJacobian.BareDeformation.exists_cocycle_of_isRegluingBy
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation f₁ L₁ B) (hD : D₀.IsRegluingBy 𝒰 τ D) :
    ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r j)
            = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0 := by sorry
