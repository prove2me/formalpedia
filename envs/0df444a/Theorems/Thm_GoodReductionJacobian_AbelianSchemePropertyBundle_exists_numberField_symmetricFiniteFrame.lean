-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_numberField_symmetricFiniteFrame
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_numberField_symmetricFiniteFrame
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:56.064137+00:00
-- url     : https://prove2.me/theorems/36aaec25-ac5e-468d-a651-d4b5d90ae69f
-- title:
--   An abelian scheme acquires a symmetric finite frame over a number field
-- statement:
--   Let $A→\operatorname{Spec}ℚ$ be an abelian scheme equipped with a commutative relative group law $G$. Then there exists a number field $F$ such that, after base change from $ℚ$ to $F$, the resulting group scheme admits a symmetric finite frame: $$∃F/ℚ\text{ a number field},\quad \operatorname{SymmetricFiniteFrame}(A_F,G_F)\neq∅.$$ This provides finite affine data for constructing an integral finite-flat model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open GoodReductionJacobian
open GoodReductionJacobian.AbelianSchemePropertyBundle

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_numberField_symmetricFiniteFrame {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of ℚ))
    (G : RelativeGroupLaw ℚ f) (hc : G.IsCommutative) (hA : AbelianSchemePropertyBundle ℚ f) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F),
      Nonempty (SymmetricFiniteFrame F
        (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℚ F))) f)
        (G.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℚ F))))) := by sorry
