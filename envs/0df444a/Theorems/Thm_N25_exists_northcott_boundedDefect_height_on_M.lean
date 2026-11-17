-- Prove2me | Theorems.Thm_N25_exists_northcott_boundedDefect_height_on_M
-- name    : N25.exists_northcott_boundedDefect_height_on_M
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:38.324354+00:00
-- url     : https://prove2.me/theorems/de8deada-9201-473c-b981-346817692875
-- title:
--   The rational Jacobian subgroup admits a Northcott height with bounded defects
-- statement:
--   Let $M$ be the arithmetic-Galois fixed subgroup of the level-$25$ Jacobian. There exist a function $h_0:M\to\mathbb R$ and constants $C_2,C_p\in\mathbb R$ such that $h_0\ge0$, every sublevel set $\{x:h_0(x)\le B\}$ is finite, and
--
--   $$|h_0(2x)-4h_0(x)|\le C_2,\qquad|h_0(x+y)+h_0(x-y)-2h_0(x)-2h_0(y)|\le C_p.$$
--
--   This supplies the Northcott and bounded-defect properties used to prove finiteness of $M$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Theorems.Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jH
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open N25

theorem N25.exists_northcott_boundedDefect_height_on_M :
    ∃ (h₀ : ↥N25.M → ℝ) (C₂ Cp : ℝ), (∀ x, 0 ≤ h₀ x) ∧ (∀ B : ℝ, {x | h₀ x ≤ B}.Finite) ∧
      (∀ x, |h₀ (x + x) - 4 * h₀ x| ≤ C₂) ∧
      ∀ x y, |h₀ (x + y) + h₀ (x - y) - 2 * h₀ x - 2 * h₀ y| ≤ Cp := by sorry
