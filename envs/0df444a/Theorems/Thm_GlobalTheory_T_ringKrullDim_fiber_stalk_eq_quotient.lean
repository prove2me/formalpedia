-- Prove2me | Theorems.Thm_GlobalTheory_T_ringKrullDim_fiber_stalk_eq_quotient
-- name    : GlobalTheory.T.ringKrullDim_fiber_stalk_eq_quotient
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:26.379418+00:00
-- url     : https://prove2.me/theorems/275627fb-2ad8-4529-9920-b1451da361e1
-- title:
--   T: ring Krull Dim fiber stalk eq quotient
-- statement:
--   The T construction uses the ring Krull Dim fiber stalk eq quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimFiberStalkEqQuotientStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimFiberStalkEqQuotientStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimFiberStalkEqQuotient
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimFiberStalkEqQuotientStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ringKrullDim_fiber_stalk_eq_quotient : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b), ringKrullDim ((π.fiber b).presheaf.stalk z) = ringKrullDim (Y.presheaf.stalk (π.fiberι b z) ⧸ (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map (π.stalkMap (π.fiberι b z)).hom) := by sorry
