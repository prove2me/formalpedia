-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_tm_coe
-- name    : GlobalTheory.JR.LinDesc.tm_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:59.683309+00:00
-- url     : https://prove2.me/theorems/369134f0-6bff-4c8a-85ea-9dcc67bd8f97
-- title:
--   Lin Desc: tm coe
-- statement:
--   The Lin Desc construction uses the tm coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LeftMulTau.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LeftMulTau.lean#L73-L74

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

theorem GlobalTheory.JR.LinDesc.tm_coe (hG : A.IsGen τ p) (t : A.Kˣ) :
    ((tm A hG t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Algebra.leftMulMatrix (bas A hG) (t : A.K) := by sorry
