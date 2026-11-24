-- Prove2me | Theorems.Thm_GlobalTheory_PolarisedLattice_lattice_of_im
-- name    : GlobalTheory.PolarisedLattice.lattice_of_im
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:40:31.613067+00:00
-- url     : https://prove2.me/theorems/206de29b-aa4c-466d-890c-e27ca63b3d66
-- title:
--   Polarised Lattice: lattice of im
-- statement:
--   The Polarised Lattice construction uses the lattice of im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L73-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L73-L117

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.PolarisedLattice

theorem GlobalTheory.PolarisedLattice.lattice_of_im {L W : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] [NormedAddCommGroup W]
    [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℝ W]
    (E : LinearMap.BilinForm ℤ L) (hE : Function.Injective E) (P : L →+ W) (S : W → W →ₗ[ℂ] ℂ)
    (hS : ∀ a b, (S (P b) (P a)).im = E a b) (hr : Module.finrank ℤ L = Module.finrank ℝ W) :
    Function.Injective P ∧ DiscreteTopology P.range ∧ Submodule.span ℝ (Set.range P) = ⊤ := by sorry
