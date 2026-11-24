-- Prove2me | Theorems.Thm_GlobalTheory_JR_GLCompact_continuous_Cm
-- name    : GlobalTheory.JR.GLCompact.continuous_Cm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:23:36.613979+00:00
-- url     : https://prove2.me/theorems/0e58ec09-fa02-4aa2-8d3d-2dbbe1db92a5
-- title:
--   GLCompact: continuous Cm
-- statement:
--   The GLCompact construction uses the continuous Cm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HasCompactSupportJacquetRallisOrbitalIntegrand.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HasCompactSupportJacquetRallisOrbitalIntegrand.lean#L27-L32

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

theorem GlobalTheory.JR.GLCompact.continuous_Cm {k : Type} [NormedField k] {r : ℕ} : Continuous (fun Y : Gl r k => Cm Y) := by sorry
