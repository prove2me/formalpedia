-- Prove2me | Theorems.Thm_GlobalTheory_nsmul_some_map_eq_zero_iff
-- name    : GlobalTheory.nsmul_some_map_eq_zero_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:13:14.421826+00:00
-- url     : https://prove2.me/theorems/4b34cc0e-855b-41a0-975c-f3198b4dd1e1
-- title:
--   Global Theory: nsmul some map eq zero iff
-- statement:
--   The Global Theory construction uses the nsmul some map eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TorsionPointTransportEmbedding.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TorsionPointTransportEmbedding.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TorsionPointTransportEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve

theorem GlobalTheory.nsmul_some_map_eq_zero_iff {F K : Type} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    (i : F →+* K) (W : WeierstrassCurve F) (x y : F) (N : ℕ)
    (h₀ : W.toAffine.Nonsingular x y) (h : (W.map i).toAffine.Nonsingular (i x) (i y)) :
    N • (Affine.Point.some (i x) (i y) h) = 0 ↔ N • (Affine.Point.some x y h₀) = 0 := by sorry
