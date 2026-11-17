-- Prove2me | Theorems.Thm_N25_n5Surj
-- name    : N25.n5Surj
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:32.896763+00:00
-- url     : https://prove2.me/theorems/7214aee1-6ab6-4e1e-834d-c66c1c2cc5a2
-- title:
--   The locally fixed subgroup has finite-index $71$-divisibility
-- statement:
--   Let $M_5≤J$ be the subgroup fixed by the chosen local Galois action at $5$. There exists a subgroup $U≤M_5$ such that $M_5/U$ is finite and multiplication by $71$ is surjective on $U$: $$|M_5/U|<∞,\qquad [71]:U↠U.$$ This is the local finite-index divisibility input for the Kummer argument at $5$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalFiveCondition
import Definitions.Def_N25_RatPointModel
import Definitions.Def_N25_LocalCarrier
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed
import Definitions.Def_N25_LocalFiveIntegralPoints
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing

set_option autoImplicit false
noncomputable section
open N25
local instance instL_N25_n5Surj_bfd51b_i2ee859 : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem N25.n5Surj : N5Surj := by sorry
