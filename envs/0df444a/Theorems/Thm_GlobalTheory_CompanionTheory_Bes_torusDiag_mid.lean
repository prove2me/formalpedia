-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusDiag_mid
-- name    : GlobalTheory.CompanionTheory.Bes.torusDiag_mid
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:44:15.667956+00:00
-- url     : https://prove2.me/theorems/272a53ac-3db9-4a63-8add-3a4b57e19086
-- title:
--   Bes: torus Diag mid
-- statement:
--   The Bes construction uses the torus Diag mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/TorusMovesCharacter.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/WeylGroupActions/TorusMovesCharacter.lean#L49-L52

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

theorem GlobalTheory.CompanionTheory.Bes.torusDiag_mid (k : ℕ) {r : ℕ} (c : Fin r → ℂ) (i : Fin (2 * r + k + 1))
    (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : torusDiag k c i = 1 := by sorry
