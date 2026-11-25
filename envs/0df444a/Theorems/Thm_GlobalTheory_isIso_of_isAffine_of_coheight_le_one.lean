-- Prove2me | Theorems.Thm_GlobalTheory_isIso_of_isAffine_of_coheight_le_one
-- name    : GlobalTheory.isIso_of_isAffine_of_coheight_le_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:38.086258+00:00
-- url     : https://prove2.me/theorems/5380d064-614d-43d1-b1f6-f38d9b1adbaf
-- title:
--   Global Theory: is Iso of is Affine of coheight le one
-- statement:
--   The Global Theory construction uses the is Iso of is Affine of coheight le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfIsAffineOpenOfRingKrullDimLeOne.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfIsAffineOpenOfRingKrullDimLeOne.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfIsAffineOpenOfRingKrullDimLeOne
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory

theorem GlobalTheory.isIso_of_isAffine_of_coheight_le_one {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] [IsAffine X] [IsAffine Y] (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) : IsIso f := by sorry
