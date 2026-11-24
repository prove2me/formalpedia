-- Prove2me | Theorems.Thm_GlobalTheory_JR_GLCompact_Bm_act
-- name    : GlobalTheory.JR.GLCompact.Bm_act
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:23:38.865798+00:00
-- url     : https://prove2.me/theorems/65545f39-b0ba-40a6-a1f8-de2302df7d34
-- title:
--   GLCompact: Bm act
-- statement:
--   The GLCompact construction uses the Bm act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HasCompactSupportJacquetRallisOrbitalIntegrand.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HasCompactSupportJacquetRallisOrbitalIntegrand.lean#L9-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportJacquetRallisOrbitalIntegrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLCompact

theorem GlobalTheory.JR.GLCompact.Bm_act {k : Type} [CommRing k] {r : ℕ} (g : GL (Fin r) k) (Y : Gl r k) :
    Bm (act g Y) = (g : Matrix (Fin r) (Fin r) k) * Bm Y := by sorry
