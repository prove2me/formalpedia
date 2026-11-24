-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmTangent_norm_pow_sub_pow_le
-- name    : GlobalTheory.CompanionTheory.SmTangent.norm_pow_sub_pow_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:09.601366+00:00
-- url     : https://prove2.me/theorems/cf439272-064f-4cce-ad72-fd37f4a41124
-- title:
--   Sm Tangent: norm pow sub pow le
-- statement:
--   The Sm Tangent construction uses the norm pow sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurve.lean#L22-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurve.lean#L22-L44

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmTangent
variable {A : Type*} [NormedRing A]

theorem GlobalTheory.CompanionTheory.SmTangent.norm_pow_sub_pow_le (h1 : ‖(1 : A)‖ ≤ 1) {a b : A} {C : ℝ} (hC : 1 ≤ C) (ha : ‖a‖ ≤ C)
    (hb : ‖b‖ ≤ C) (k : ℕ) : ‖a ^ k - b ^ k‖ ≤ k * C ^ k * ‖a - b‖ := by sorry
