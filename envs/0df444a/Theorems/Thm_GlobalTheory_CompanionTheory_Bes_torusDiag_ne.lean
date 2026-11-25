-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusDiag_ne
-- name    : GlobalTheory.CompanionTheory.Bes.torusDiag_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:48:57.474561+00:00
-- url     : https://prove2.me/theorems/4c649c6e-2503-4e60-843b-480dcc22dce7
-- title:
--   Bes: torus Diag ne
-- statement:
--   The Bes construction uses the torus Diag ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/TorusMovesCharacter.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/TorusMovesCharacter.lean#L42-L47

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

theorem GlobalTheory.CompanionTheory.Bes.torusDiag_ne (k : ℕ) {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0)
    (i : Fin (2 * r + k + 1)) : torusDiag k c i ≠ 0 := by sorry
