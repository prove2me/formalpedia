-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_continuous_pt
-- name    : GlobalTheory.JR.LinDesc.Swap.continuous_pt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:34:02.848878+00:00
-- url     : https://prove2.me/theorems/a19cde56-b76b-4beb-b0b9-33271e902c0f
-- title:
--   Swap: continuous pt
-- statement:
--   The Swap construction uses the continuous pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearDescentPartialFourierEqFourierDescent.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearDescentPartialFourierEqFourierDescent.lean#L77-L84

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
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] (A : Et F E)

theorem GlobalTheory.JR.LinDesc.Swap.continuous_pt {r : ℕ} {τ : A.K} {p : Fin r → F} (hG : A.IsGen τ p) (lam : F) :
    Continuous (fun q : A.K × A.K => pt A hG lam q.1 q.2) := by sorry
