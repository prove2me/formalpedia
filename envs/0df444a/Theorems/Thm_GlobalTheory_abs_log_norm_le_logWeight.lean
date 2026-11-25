-- Prove2me | Theorems.Thm_GlobalTheory_abs_log_norm_le_logWeight
-- name    : GlobalTheory.abs_log_norm_le_logWeight
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:22.16661+00:00
-- url     : https://prove2.me/theorems/117b12cc-defb-41e9-b101-93f74c403efe
-- title:
--   Global Theory: abs log norm le log Weight
-- statement:
--   The Global Theory construction uses the abs log norm le log Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L41-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ X : Type*}

theorem GlobalTheory.abs_log_norm_le_logWeight {S : Finset κ} (z : κ → ℂ) {j : κ} (hj : j ∈ S) :
    |Real.log ‖z j‖| ≤ lwP₂ S z := by sorry
