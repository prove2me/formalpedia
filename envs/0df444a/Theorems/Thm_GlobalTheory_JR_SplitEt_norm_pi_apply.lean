-- Prove2me | Theorems.Thm_GlobalTheory_JR_SplitEt_norm_pi_apply
-- name    : GlobalTheory.JR.SplitEt.norm_pi_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:36:40.195782+00:00
-- url     : https://prove2.me/theorems/6eff0fe6-b553-45ca-b658-3bcddbea1063
-- title:
--   Split Et: norm pi apply
-- statement:
--   The Split Et construction uses the norm pi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSplitEtaleHermitianPairIsometry.lean#L42-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSplitEtaleHermitianPairIsometry.lean#L42-L57

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

theorem GlobalTheory.JR.SplitEt.norm_pi_apply (r : ℕ) (y : Fin r → E) (i : Fin r) :
    Algebra.norm (Fin r → F) y i = Algebra.norm F (y i) := by sorry
