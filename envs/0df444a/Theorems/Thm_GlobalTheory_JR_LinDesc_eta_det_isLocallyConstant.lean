-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_eta_det_isLocallyConstant
-- name    : GlobalTheory.JR.LinDesc.eta_det_isLocallyConstant
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:33:29.808062+00:00
-- url     : https://prove2.me/theorems/38c0f51a-feb3-4094-86bd-00bea6959c91
-- title:
--   Lin Desc: eta det is Locally Constant
-- statement:
--   The Lin Desc construction uses the eta det is Locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportJacquetRallisDesc.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportJacquetRallisDesc.lean#L25-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportJacquetRallisDesc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc

theorem GlobalTheory.JR.LinDesc.eta_det_isLocallyConstant {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] (r : ℕ) :
    IsLocallyConstant (fun g : GL (Fin r) F => eta ((g : Matrix (Fin r) (Fin r) F).det)) := by sorry
