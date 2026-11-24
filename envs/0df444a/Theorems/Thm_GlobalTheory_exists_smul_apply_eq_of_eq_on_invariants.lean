-- Prove2me | Theorems.Thm_GlobalTheory_exists_smul_apply_eq_of_eq_on_invariants
-- name    : GlobalTheory.exists_smul_apply_eq_of_eq_on_invariants
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:38.626259+00:00
-- url     : https://prove2.me/theorems/028c6b40-4f06-4b2b-b928-882d251296d4
-- title:
--   Global Theory: exists smul apply eq of eq on invariants
-- statement:
--   The Global Theory construction uses the exists smul apply eq of eq on invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulApplyEqOfEqOnInvariants.lean#L15-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulApplyEqOfEqOnInvariants.lean#L15-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory

theorem GlobalTheory.exists_smul_apply_eq_of_eq_on_invariants {G B D : Type*} [Group G] [Finite G] [CommRing B]
    [CommRing D] [IsDomain D] [MulSemiringAction G B] (x y : B →+* D)
    (h : ∀ b, (∀ g : G, g • b = b) → x b = y b) (b : B) : ∃ g : G, y b = x (g • b) := by sorry
