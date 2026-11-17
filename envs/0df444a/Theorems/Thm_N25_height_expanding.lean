-- Prove2me | Theorems.Thm_N25_height_expanding
-- name    : N25.height_expanding
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:48.060794+00:00
-- url     : https://prove2.me/theorems/e141bb84-d56a-488c-a0f7-8a41fc1b71f7
-- title:
--   The selected endomorphism expands a Northcott height by $7/3$
-- statement:
--   Let $M=J^{G_{ℚ}}$ be the rational fixed subgroup and let $π=2+4γ+γ^2$ be the selected endomorphism restricted to $M$. There exists a function $q:M→ℝ$ whose every sublevel set is finite and which satisfies $$\{x∈M:q(x)≤B\}\text{ is finite for every }B∈ℝ,\qquad \frac{7}{3}q(x)≤q(πx)\text{ for every }x∈M.$$ This expanding Northcott function is the height input for proving finiteness of the Mordell–Weil subgroup.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_piEnd_mem_M
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm
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
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_N25_Alg_exists_canonicalQuadratic_of_boundedDefects
import Theorems.Thm_N25_Alg_exists_invariant_quadratic_of_pow_five
import Theorems.Thm_N25_Alg_quadratic_norm71_expansion

set_option autoImplicit false
open N25

theorem N25.height_expanding :
    ∃ q : ↥N25.M → ℝ, (∀ B : ℝ, {x | q x ≤ B}.Finite) ∧
      ∀ x : ↥N25.M, (7 / 3 : ℝ) * q x ≤ q ⟨N25.piEnd x, N25.piEnd_mem_M x.2⟩ := by sorry
