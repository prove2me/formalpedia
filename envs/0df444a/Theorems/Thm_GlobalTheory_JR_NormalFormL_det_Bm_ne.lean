-- Prove2me | Theorems.Thm_GlobalTheory_JR_NormalFormL_det_Bm_ne
-- name    : GlobalTheory.JR.NormalFormL.det_Bm_ne
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:34:06.805309+00:00
-- url     : https://prove2.me/theorems/02fc2f93-6357-4c86-8a32-d5f9a2e31d07
-- title:
--   Normal Form L: det Bm ne
-- statement:
--   The Normal Form L construction uses the det Bm ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L181-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L181-L184

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}

theorem GlobalTheory.JR.NormalFormL.det_Bm_ne (Y : Gl r k) (h : Delta (inv Y) ≠ 0) : (Bm Y).det ≠ 0 := by sorry
