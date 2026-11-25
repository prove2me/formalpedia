-- Prove2me | Theorems.Thm_GlobalTheory_LocLift_lattice_comp
-- name    : GlobalTheory.LocLift.lattice_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:40:08.737035+00:00
-- url     : https://prove2.me/theorems/00cd9874-bd84-453e-a5f8-800657065747
-- title:
--   Loc Lift: lattice comp
-- statement:
--   The Loc Lift construction uses the lattice comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HolomorphicMapModuliLiftsLocallyToPeriods.lean#L78-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HolomorphicMapModuliLiftsLocallyToPeriods.lean#L78-L91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicMapModuliLiftsLocallyToPeriods
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
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

theorem GlobalTheory.LocLift.lattice_comp {La : Type} [AddCommGroup La] {P : La →+ (Fin g → ℂ)} (h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
    {P' : La →+ (Fin g → ℂ)} (hP : ∀ x, h (P' x) = P x) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hd : DiscreteTopology P.range) : Submodule.span ℝ (Set.range P') = ⊤ ∧ DiscreteTopology P'.range := by sorry
