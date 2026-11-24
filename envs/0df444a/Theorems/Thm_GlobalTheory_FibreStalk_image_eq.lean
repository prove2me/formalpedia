-- Prove2me | Theorems.Thm_GlobalTheory_FibreStalk_image_eq
-- name    : GlobalTheory.FibreStalk.image_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:22.989801+00:00
-- url     : https://prove2.me/theorems/5e4ad2d6-d33b-424a-aa11-94525077ca5e
-- title:
--   Fibre Stalk: image eq
-- statement:
--   The Fibre Stalk construction uses the image eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimFiberStalkEqQuotient.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimFiberStalkEqQuotient.lean#L13-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimFiberStalkEqQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.FibreStalk

theorem GlobalTheory.FibreStalk.image_eq (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) : π (π.fiberι b z) = b := by sorry
