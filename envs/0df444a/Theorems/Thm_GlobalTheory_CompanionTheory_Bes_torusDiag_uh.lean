-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusDiag_uh
-- name    : GlobalTheory.CompanionTheory.Bes.torusDiag_uh
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:49:17.173875+00:00
-- url     : https://prove2.me/theorems/52ed48fd-eed7-4469-920d-1d827d200143
-- title:
--   Bes: torus Diag uh
-- statement:
--   The Bes construction uses the torus Diag uh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/TorusMovesCharacter.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/TorusMovesCharacter.lean#L76-L86

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

theorem GlobalTheory.CompanionTheory.Bes.torusDiag_uh (k : ℕ) {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) :
    Matrix.diagonal (torusDiag k c) ∈ UH (Hpk k r) := by sorry
