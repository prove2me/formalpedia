-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_continuous_eta_det
-- name    : GlobalTheory.JR.LinDesc.Swap.continuous_eta_det
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:34:27.845135+00:00
-- url     : https://prove2.me/theorems/e08b5cff-e707-4b9e-addb-84c770e8ec51
-- title:
--   Swap: continuous eta det
-- statement:
--   The Swap construction uses the continuous eta det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearDescentPartialFourierEqFourierDescent.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearDescentPartialFourierEqFourierDescent.lean#L32-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc GlobalTheory.JR.LinDesc.Swap

theorem GlobalTheory.JR.LinDesc.Swap.continuous_eta_det {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] (r : ℕ) :
    Continuous (fun g : GL (Fin r) F => eta ((g : Matrix (Fin r) (Fin r) F).det)) := by sorry
