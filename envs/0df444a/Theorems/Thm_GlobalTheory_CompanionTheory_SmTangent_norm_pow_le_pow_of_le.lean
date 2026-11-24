-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmTangent_norm_pow_le_pow_of_le
-- name    : GlobalTheory.CompanionTheory.SmTangent.norm_pow_le_pow_of_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:30.209412+00:00
-- url     : https://prove2.me/theorems/9256a4f7-d427-49ac-b700-32ab4c33bca6
-- title:
--   Sm Tangent: norm pow le pow of le
-- statement:
--   The Sm Tangent construction uses the norm pow le pow of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurve.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraOfTangentCurve.lean#L12-L20

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

theorem GlobalTheory.CompanionTheory.SmTangent.norm_pow_le_pow_of_le (h1 : ‖(1 : A)‖ ≤ 1) {b : A} {C : ℝ} (hC : 1 ≤ C) (hb : ‖b‖ ≤ C) (k : ℕ) :
    ‖b ^ k‖ ≤ C ^ k := by sorry
