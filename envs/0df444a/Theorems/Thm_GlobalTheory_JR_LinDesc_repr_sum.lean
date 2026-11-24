-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_repr_sum
-- name    : GlobalTheory.JR.LinDesc.repr_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:34:26.385956+00:00
-- url     : https://prove2.me/theorems/7bfe7d10-f1c6-4bcc-935a-c935041df608
-- title:
--   Lin Desc: repr sum
-- statement:
--   The Lin Desc construction uses the repr sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LeftMulTau.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LeftMulTau.lean#L39-L45

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

theorem GlobalTheory.JR.LinDesc.repr_sum (hG : A.IsGen τ p) (c : Fin r → F) :
    (LinDesc.bas A hG).repr (∑ i, c i • τ ^ (i : ℕ)) = Finsupp.equivFunOnFinite.symm c := by sorry
