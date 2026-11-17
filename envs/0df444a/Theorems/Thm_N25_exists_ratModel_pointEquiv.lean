-- Prove2me | Theorems.Thm_N25_exists_ratModel_pointEquiv
-- name    : N25.exists_ratModel_pointEquiv
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:33:26.044168+00:00
-- url     : https://prove2.me/theorems/2c876d54-953f-4736-b964-b3306ad53bec
-- title:
--   The rational fixed subgroup is the group of rational points of an abelian scheme
-- statement:
--   Let $M$ be the arithmetic-Galois fixed subgroup of the Jacobian. There exist a scheme $A$ over $\operatorname{Spec}\mathbb Q$, a relative group law $G$ on $A$, and an equivalence $e:M\simeq A(\mathbb Q)$ such that $G$ is commutative, $A$ satisfies the stated abelian-scheme property bundle, and
--
--   $$e(x+y)=G(e(x),e(y))\qquad(x,y\in M).$$
--
--   This realizes the abstract rational subgroup as rational points of a genuine commutative abelian model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Theorems.Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jH
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open N25

theorem N25.exists_ratModel_pointEquiv :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of ℚ)) (G : RelativeGroupLaw ℚ f)
      (e : ↥N25.M ≃ Scheme.KPoint f),
      G.IsCommutative ∧ AbelianSchemePropertyBundle ℚ f ∧
      ∀ x y : ↥N25.M, e (x + y) = G.mul (𝟙 _) (e x) (e y) := by sorry
