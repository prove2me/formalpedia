-- Prove2me | Theorems.Thm_GlobalTheory_PowerDifferenceNormInertiaEigenvalues_norm_pow_sub_pow_le
-- name    : GlobalTheory.PowerDifferenceNormInertiaEigenvalues.norm_pow_sub_pow_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:53:58.050842+00:00
-- url     : https://prove2.me/theorems/41cd151d-1974-42f2-9eb0-3aa1113bad44
-- title:
--   Power Difference Norm Inertia Eigenvalues: norm pow sub pow le
-- statement:
--   The Power Difference Norm Inertia Eigenvalues construction uses the norm pow sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImportsLast.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImportsLast.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerDifferenceNormInertiaEigenvalues
universe u_1

theorem GlobalTheory.PowerDifferenceNormInertiaEigenvalues.norm_pow_sub_pow_le {C : Type u_1} [NormedField C] [IsUltrametricDist C] {x y : C}
    (hx : ‖x‖ ≤ (1 : ℝ)) (hy : ‖y‖ ≤ (1 : ℝ)) (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by sorry
