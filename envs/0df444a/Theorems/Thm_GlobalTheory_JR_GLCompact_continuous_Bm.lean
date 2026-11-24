-- Prove2me | Theorems.Thm_GlobalTheory_JR_GLCompact_continuous_Bm
-- name    : GlobalTheory.JR.GLCompact.continuous_Bm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:23:34.948803+00:00
-- url     : https://prove2.me/theorems/d525165a-2d85-4c90-869e-5694d054acc8
-- title:
--   GLCompact: continuous Bm
-- statement:
--   The GLCompact construction uses the continuous Bm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HasCompactSupportJacquetRallisOrbitalIntegrand.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HasCompactSupportJacquetRallisOrbitalIntegrand.lean#L21-L25

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

theorem GlobalTheory.JR.GLCompact.continuous_Bm {k : Type} [NormedField k] {r : ℕ} : Continuous (fun Y : Gl r k => Bm Y) := by sorry
