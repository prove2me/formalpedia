-- Prove2me | Theorems.Thm_GlobalTheory_JR_SplitEt_trace_pi_apply
-- name    : GlobalTheory.JR.SplitEt.trace_pi_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:41.780983+00:00
-- url     : https://prove2.me/theorems/6df33266-3ac6-42f3-9f26-759810452431
-- title:
--   Split Et: trace pi apply
-- statement:
--   The Split Et construction uses the trace pi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSplitEtaleHermitianPairIsometry.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSplitEtaleHermitianPairIsometry.lean#L59-L62

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSplitEtaleHermitianPairIsometry
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SplitEt
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem GlobalTheory.JR.SplitEt.trace_pi_apply (r : ℕ) (z : Fin r → E) : Algebra.trace E (Fin r → E) z = ∑ i, z i := by sorry
