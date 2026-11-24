-- Prove2me | Theorems.Thm_GlobalTheory_FibreStalk_fromSpecResidueField_eq
-- name    : GlobalTheory.FibreStalk.fromSpecResidueField_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:33.476289+00:00
-- url     : https://prove2.me/theorems/ce60d763-7a69-418a-8e9f-7cca18f4f857
-- title:
--   Fibre Stalk: from Spec Residue Field eq
-- statement:
--   The Fibre Stalk construction uses the from Spec Residue Field eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimFiberStalkEqQuotient.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimFiberStalkEqQuotient.lean#L7-L11

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

theorem GlobalTheory.FibreStalk.fromSpecResidueField_eq {B : Scheme.{0}} {x b : B} (h : x = b) :
    B.fromSpecResidueField b =
      Spec.map (B.residue x ≫ (B.residueFieldCongr h).hom) ≫ B.fromSpecStalk x := by sorry
