-- Prove2me | Theorems.Thm_GlobalTheory_LinDescent_sum_coeff_eq_zero_of_linearIndependent
-- name    : GlobalTheory.LinDescent.sum_coeff_eq_zero_of_linearIndependent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:08:30.755665+00:00
-- url     : https://prove2.me/theorems/394f524e-6207-4ee5-9b35-315da554c2b5
-- title:
--   Lin Descent: sum coeff eq zero of linear Independent
-- statement:
--   The Lin Descent construction uses the sum coeff eq zero of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDescentOfInvGenOfInvariants.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDescentOfInvGenOfInvariants.lean#L20-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfInvGenOfInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.LinDescent.sum_coeff_eq_zero_of_linearIndependent {R M ι C : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [Fintype C] [DecidableEq ι] {v : ι → M} (hv : LinearIndependent R v) (p : C → ι)
    (a : C → R) (h : ∑ c, a c • v (p c) = 0) (i : ι) : ∑ c, (if p c = i then a c else 0) = 0 := by sorry
