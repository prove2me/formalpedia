-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_factor_inf_of_local_lifts_factor_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_factor_inf_of_local_lifts_factor_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/357297a5-700b-5e2e-85be-4b07a105e6ae
-- title:
--   Refining four chart factorisations to a common overlap
-- statement:
--   Let $B$ be a local Artinian commutative ring and $B_1$ a commutative $B$-algebra such that the structure map $B \to B_1$ is surjective with kernel contained in the maximal ideal of $B$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ be a scheme over $B_1$ equipped with a relative group law $L_1$, and let $D_0$ and $D$ be two bare deformations of $(f_1, L_1)$ over $B$: each consists of a scheme with a structure morphism to $\operatorname{Spec} B$, a commutative relative group law on it, smoothness, properness and connectedness of fibres, and a morphism from $A_1$ making the square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ cartesian and compatible with the group laws. Let $\mathcal{U}$ be an ordered affine cover of $D_0.A$, i.e. a finite linearly ordered family of affine opens $U_i$ with $\bigsqcup_i U_i = \top$, and let $\varphi_1 : A_1 \to A_1$ be an arbitrary endomorphism. The data further comprise, for each $i$, morphisms $m_i : U_i \to D_0.A$ and $m'_i : U_i \to D.A$ with $(D_0.g \mid_{U_i}) \gg m_i$ and $(D_0.g \mid_{U_i}) \gg m'_i$ equal to the inclusion of $D_0.g^{-1}U_i$ followed by $\varphi_1$ and then $D_0.g$, respectively $D.g$, together with morphisms $\iota_i : U_i \to D.A$ satisfying $(D_0.g \mid_{U_i}) \gg \iota_i = \text{incl} \gg D.g$. Finally, indices $i, i', j, j'$ are given, together with opens $W_0 \le U_j$ and $W_1 \le U_{j'}$ of $D_0.A$ and morphisms $n_0, n'_0 : W_0 \to U_i$ and $n_1, n'_1 : W_1 \to U_{i'}$ such that $n_0$ followed by $U_i \hookrightarrow D_0.A$ equals $W_0 \hookrightarrow U_j$ followed by $m_j$, $n'_0$ followed by $\iota_i$ equals $W_0 \hookrightarrow U_j$ followed by $m'_j$, and likewise $n_1$ followed by $U_{i'} \hookrightarrow D_0.A$ equals $W_1 \hookrightarrow U_{j'}$ followed by $m_{j'}$ and $n'_1$ followed by $\iota_{i'}$ equals $W_1 \hookrightarrow U_{j'}$ followed by $m'_{j'}$. The conclusion asserts the existence of four morphisms $p, p', q, q' : W_0 \sqcap W_1 \to U_i \sqcap U_{i'}$ such that $p$ and $p'$ followed by $U_i \sqcap U_{i'} \hookrightarrow U_i$ agree with $W_0 \sqcap W_1 \hookrightarrow W_0$ followed by $n_0$, respectively $n'_0$, and $q$ and $q'$ followed by $U_i \sqcap U_{i'} \hookrightarrow U_{i'}$ agree with $W_1 \sqcap W_0 \hookrightarrow W_1$ followed by $n_1$, respectively $n'_1$.
--
--   This is the re-gluing step for the obstruction to lifting an endomorphism of $A_1$ to a bare deformation: chartwise factorisations of the local lifts through a single chart are refined so that, on the overlap of two refinement opens, all four factorisations land in the intersection of the two charts, where they can be compared. It is used in the construction of the obstruction cocycle, in the two lemmas computing the difference of the induced maps as a coboundary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_factor_inf_of_local_lifts_factor_bare.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.exists_factor_inf_of_local_lifts_factor_bare
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover)
    (φ₁ : A₁ ⟶ A₁)

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)

    (D : BareDeformation f₁ L₁ B)
    (ιD : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιD i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)

    (mp : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hmpμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mp i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D.g)

    (i i' j j' : 𝒰.ι) (W₀ W₁ : D₀.A.Opens) (h₀ : W₀ ≤ 𝒰.U j) (h₁ : W₁ ≤ 𝒰.U j')
    (n₀ n₀' : (↑W₀ : Scheme.{0}) ⟶ ↑(𝒰.U i)) (n₁ n₁' : (↑W₁ : Scheme.{0}) ⟶ ↑(𝒰.U i'))
    (hn₀ : n₀ ≫ (𝒰.U i).ι = D₀.A.homOfLE h₀ ≫ m j) (hn₀' : n₀' ≫ ιD i = D₀.A.homOfLE h₀ ≫ mp j)
    (hn₁ : n₁ ≫ (𝒰.U i').ι = D₀.A.homOfLE h₁ ≫ m j') (hn₁' : n₁' ≫ ιD i' = D₀.A.homOfLE h₁ ≫ mp j') :
    ∃ (p p' q q' : (↑(W₀ ⊓ W₁) : Scheme.{0}) ⟶ ↑(𝒰.U i ⊓ 𝒰.U i')),
      p ≫ D₀.A.homOfLE inf_le_left = D₀.A.homOfLE inf_le_left ≫ n₀ ∧
      p' ≫ D₀.A.homOfLE inf_le_left = D₀.A.homOfLE inf_le_left ≫ n₀' ∧
      q ≫ D₀.A.homOfLE inf_le_right = D₀.A.homOfLE inf_le_right ≫ n₁ ∧
      q' ≫ D₀.A.homOfLE inf_le_right = D₀.A.homOfLE inf_le_right ≫ n₁' := by sorry
