-- Prove2me | Theorems.Thm_GlobalTheory_norm_mul_sub_one_le_of_norm_sub_one_le
-- name    : GlobalTheory.norm_mul_sub_one_le_of_norm_sub_one_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:10.273434+00:00
-- url     : https://prove2.me/theorems/5871329f-5ce0-414e-a6cf-a22e6a9a19b8
-- title:
--   Global Theory: norm mul sub one le of norm sub one le
-- statement:
--   The Global Theory construction uses the norm mul sub one le of norm sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CongruenceSubgroupsGLPadic.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CongruenceSubgroupsGLPadic.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricMatrixInvNearOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixMulEntryNormLeUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CongruenceSubgroupsGLPadic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.norm_mul_sub_one_le_of_norm_sub_one_le {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] (X Y : Matrix n n E) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ t) (hY : ∀ i j, ‖(Y - 1) i j‖ ≤ t) :
    ∀ i j, ‖(X * Y - 1) i j‖ ≤ t := by sorry
