-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torus_moves_character
-- name    : GlobalTheory.CompanionTheory.Bes.torus_moves_character
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:48.785409+00:00
-- url     : https://prove2.me/theorems/23119baf-b99a-5c09-bf4f-8ec5e9b0b4e7
-- title:
--   Bes: torus moves character
-- statement:
--   The Bes construction uses the torus moves character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/TorusMovesCharacter.lean#L106-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/TorusMovesCharacter.lean#L106-L161

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_TorusMovesCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Bes
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts

theorem GlobalTheory.CompanionTheory.Bes.torus_moves_character :
    ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ a, c a ≠ 0) → ∃ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, a * h = h * a) ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, a * m * a⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ a⁻¹ * m * a ∈ Formalism.QuantumDeterminants.Nset k r ∧ PI.BesselL2FixAtZero.psiGen k r z (fun _ => 1) (a * m * a⁻¹) = PI.BesselL2FixAtZero.psiGen k r z c m) := by sorry
