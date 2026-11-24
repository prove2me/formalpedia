-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_Delta_map
-- name    : GlobalTheory.JR.Step.Delta_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:37:23.705557+00:00
-- url     : https://prove2.me/theorems/1e5a15e3-f250-4376-bac1-6f8ff2056192
-- title:
--   Step: Delta map
-- statement:
--   The Step construction uses the Delta map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftMatch.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftMatch.lean#L42-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k')

theorem GlobalTheory.JR.Step.Delta_map (a : Inv r k) : Delta (a.map φ) = φ (Delta a) := by sorry
