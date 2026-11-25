-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_act_tm
-- name    : GlobalTheory.JR.LinDesc.act_tm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:30.824157+00:00
-- url     : https://prove2.me/theorems/24875158-1f04-51ee-83b0-bc8fe62ca27f
-- title:
--   Lin Desc: act tm
-- statement:
--   The Lin Desc construction uses the act tm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LeftMulTau.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LeftMulTau.lean#L94-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
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
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem GlobalTheory.JR.LinDesc.act_tm (hG : A.IsGen τ p) (lam : F) (t : A.Kˣ) (b c : A.K) :
    act (tm A hG t) (pt A hG lam b c) = pt A hG lam ((t : A.K) * b) (((t⁻¹ : A.Kˣ) : A.K) * c) := by sorry
