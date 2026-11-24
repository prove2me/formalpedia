-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_continuous_act
-- name    : GlobalTheory.JR.LinDesc.Swap.continuous_act
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:34:12.11614+00:00
-- url     : https://prove2.me/theorems/361eed7d-4741-4ef7-b041-62ccebe3d60e
-- title:
--   Swap: continuous act
-- statement:
--   The Swap construction uses the continuous act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearDescentPartialFourierEqFourierDescent.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearDescentPartialFourierEqFourierDescent.lean#L52-L62

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

theorem GlobalTheory.JR.LinDesc.Swap.continuous_act {F : Type} [NontriviallyNormedField F] (r : ℕ) :
    Continuous (fun z : GL (Fin r) F × Gl r F => act z.1 z.2) := by sorry
