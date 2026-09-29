-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_snd_appLE_mul_tangentPoints_eq_add
-- name    : GoodReductionJacobian.RelativeGroupLaw.snd_appLE_mul_tangentPoints_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/4e553464-71ca-5bba-b6a8-dc9b1f014687
-- title:
--   Tangent vectors at the unit add under a relative group law
-- statement:
--   Let $K$ be a field, $A$ a scheme, and $f : A \to \operatorname{Spec} K$ a morphism, and let $L$ be a relative group law on $f$: an assignment, to each $T$ and each $t : T \to \operatorname{Spec} K$, of multiplication, unit and inverse operations on the set of $\varphi : T \to A$ with $\varphi \circ f$ (diagrammatically $\varphi \mathbin{\text{then}} f$) equal to $t$, satisfying associativity, the two unit laws, left inverse, and naturality in $T$. Let $V$ be a $K$-module, viewed with compatible left and opposite actions acting centrally, and write $R = K \oplus V$ for the trivial square-zero extension $\mathtt{TrivSqZeroExt}\ K\ V$. Let $v_1, v_2$ be $V$-valued tangent points of $f$ at the unit $(L.\mathrm{one}(\mathbb{1}))$: morphisms $v : \operatorname{Spec} R \to A$ over the structure map $\operatorname{Spec} R \to \operatorname{Spec} K$ whose restriction along the base point $\operatorname{Spec} K \to \operatorname{Spec} R$ is that unit section. Let $W$ be an open of $A$, $a \in \Gamma(A, W)$, and assume that $v_1$, $v_2$ and their product $\mu = L.\mathrm{mul}$ applied to $v_1, v_2$ over $\operatorname{Spec} R \to \operatorname{Spec} K$ each pull $W$ back to the whole of $\operatorname{Spec} R$. Then, identifying $\Gamma(\operatorname{Spec} R, \top)$ with $R$ via `Scheme.ΓSpecIso`, the $V$-component of $\mu^\sharp a$ equals the sum of the $V$-components of $v_1^\sharp a$ and $v_2^\sharp a$.
--
--   This is the infinitesimal additivity of a group law at its unit, $d\mu_{(e,e)} = dp_1 + dp_2$, expressed on sections over an open set containing the images of the three $\operatorname{Spec}(K \oplus V)$-points. It is used to show that the point derivations attached to the product of two tangent vectors are the sum of the two point derivations, in [`GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero`](thm.html#GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_snd_appLE_mul_tangentPoints_eq_add.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian Scheme.TwoAffineOpenCover

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.snd_appLE_mul_tangentPoints_eq_add
    {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
    (v₁ v₂ : TangentPoints f (L.one (𝟙 _)).1 V)
    (W : A.Opens) (a : Γ(A, W))
    (h₁ : ⊤ ≤ v₁.1 ⁻¹ᵁ W) (h₂ : ⊤ ≤ v₂.1 ⁻¹ᵁ W)
    (hμ : ⊤ ≤ (L.mul (SquareZero.toBase K V) ⟨v₁.1, v₁.2.1⟩ ⟨v₂.1, v₂.2.1⟩).1 ⁻¹ᵁ W) :
    (((L.mul (SquareZero.toBase K V) ⟨v₁.1, v₁.2.1⟩ ⟨v₂.1, v₂.2.1⟩).1.appLE W ⊤ hμ ≫
        (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K V))).hom).hom a).snd =
      ((v₁.1.appLE W ⊤ h₁ ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K V))).hom).hom a).snd +
      ((v₂.1.appLE W ⊤ h₂ ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K V))).hom).hom a).snd := by sorry
