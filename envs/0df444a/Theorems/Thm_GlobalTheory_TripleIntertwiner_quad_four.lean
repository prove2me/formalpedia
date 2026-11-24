-- Prove2me | Theorems.Thm_GlobalTheory_TripleIntertwiner_quad_four
-- name    : GlobalTheory.TripleIntertwiner.quad_four
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:25.650198+00:00
-- url     : https://prove2.me/theorems/f4e8438b-ed2b-43f6-b00f-9dc4b3962f49
-- title:
--   Triple Intertwiner: quad four
-- statement:
--   The Triple Intertwiner construction uses the quad four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L9-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical

theorem GlobalTheory.TripleIntertwiner.quad_four {M G : Type*} [AddCommGroup M] [AddCommGroup G] (β : M →+ M →+ G) (a b c d : ℤ)
    (x y z w : M) :
    β (a • x - b • y - c • z - d • w) (a • x - b • y - c • z - d • w) +
      β (b • x + a • y - d • z + c • w) (b • x + a • y - d • z + c • w) +
      β (c • x + d • y + a • z - b • w) (c • x + d • y + a • z - b • w) +
      β (d • x - c • y + b • z + a • w) (d • x - c • y + b • z + a • w) =
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • (β x x + β y y + β z z + β w w) := by sorry
