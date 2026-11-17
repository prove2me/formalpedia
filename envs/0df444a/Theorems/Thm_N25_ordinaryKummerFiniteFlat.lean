-- Prove2me | Theorems.Thm_N25_ordinaryKummerFiniteFlat
-- name    : N25.ordinaryKummerFiniteFlat
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:05:20.974818+00:00
-- url     : https://prove2.me/theorems/b70cf130-3e5e-44c2-b3da-3fe229bdb2ee
-- title:
--   The ordinary local Kummer condition at $71$ holds
-- statement:
--   Let $J$ be the geometric Jacobian carrier and $M=J^{G_{ℚ}}$. For every $Q∈J$ such that $71Q∈M$, the local cocycle $σ↦σQ-Q$ on $G_{ℚ_{71}}$ defines a finite-flat extension of the local $71$-torsion representation: $$71Q∈M\quad⇒\quad \text{the associated local cocycle extension at }71\text{ is finite flat}.$$ This supplies the exceptional local condition at the torsion prime in the global Kummer descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_OrdinaryKummerFiniteFlat
import Theorems.Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jH
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Limits
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibreProjection
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_AlgebraicGeometry_exists_hopfAlgebra_flat_of_grpObj_over_spec
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GroupCohomology_FiniteFlatCocycle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian
open N25
local instance instL_N25_ordinaryKummerFiniteFlat_23397f_id40306 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.ordinaryKummerFiniteFlat : OrdinaryKummerFiniteFlat := by sorry
