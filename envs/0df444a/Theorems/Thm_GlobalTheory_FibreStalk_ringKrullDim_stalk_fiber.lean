-- Prove2me | Theorems.Thm_GlobalTheory_FibreStalk_ringKrullDim_stalk_fiber
-- name    : GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:24.865803+00:00
-- url     : https://prove2.me/theorems/087ceaa2-9664-4c19-964b-7e896544ba3f
-- title:
--   Fibre Stalk: ring Krull Dim stalk fiber
-- statement:
--   The Fibre Stalk construction uses the ring Krull Dim stalk fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimFiberStalkEqQuotient.lean#L94-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimFiberStalkEqQuotient.lean#L94-L101

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

theorem GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b),
    ringKrullDim ((π.fiber b).presheaf.stalk z) =
      ringKrullDim (Y.presheaf.stalk (π.fiberι b z) ⧸
        (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
          (π.stalkMap (π.fiberι b z)).hom) := by sorry
