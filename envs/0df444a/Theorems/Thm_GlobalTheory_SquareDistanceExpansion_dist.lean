-- Prove2me | Theorems.Thm_GlobalTheory_SquareDistanceExpansion_dist
-- name    : GlobalTheory.SquareDistanceExpansion.dist
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:22:43.381837+00:00
-- url     : https://prove2.me/theorems/171636e9-6f03-44f0-a085-0502367d9712
-- title:
--   Square Distance Expansion: dist
-- statement:
--   The Square Distance Expansion construction uses the dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SqId.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SqId.lean#L20-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SqId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SquareDistanceExpansion
open Matrix

theorem GlobalTheory.SquareDistanceExpansion.dist {R : Type} [CommRing R] {n d : ℕ} (a : Matrix (Fin n) (Fin d) R)
    (α : Matrix (Fin d) (Fin n) R) (A B : Matrix (Fin d) (Fin d) R) :
    a * (A + B + A * B) * α = a * A * α + a * B * α + a * A * B * α := by sorry
