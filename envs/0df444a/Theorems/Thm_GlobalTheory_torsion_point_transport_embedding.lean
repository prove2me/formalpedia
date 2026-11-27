-- Prove2me | Theorems.Thm_GlobalTheory_torsion_point_transport_embedding
-- name    : GlobalTheory.torsion_point_transport_embedding
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:49.787382+00:00
-- url     : https://prove2.me/theorems/87381e3e-3c4c-435d-844b-ed77d3cc8ee8
-- title:
--   Global Theory: torsion point transport embedding
-- statement:
--   The Global Theory construction uses the torsion point transport embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TorsionPointTransportEmbedding.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TorsionPointTransportEmbedding.lean#L18-L33

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

theorem GlobalTheory.torsion_point_transport_embedding :
    ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [DecidableEq K] [DecidableEq K'] (i : F →+* K) (j : F →+* K') (A B x y : F) (N : ℕ) (h : (⟨0, 0, 0, i A, i B⟩ : WeierstrassCurve K).toAffine.Nonsingular (i x) (i y)), N • (WeierstrassCurve.Affine.Point.some (i x) (i y) h) = 0 → ∃ h' : (⟨0, 0, 0, j A, j B⟩ : WeierstrassCurve K').toAffine.Nonsingular (j x) (j y), N • (WeierstrassCurve.Affine.Point.some (j x) (j y) h') = 0 := by sorry
