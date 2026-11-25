-- Prove2me | Theorems.Thm_GlobalTheory_FibreRegular_isRegularLocalRing_stalk_quot_maximalIdeal
-- name    : GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:10.471453+00:00
-- url     : https://prove2.me/theorems/edb24e74-68a5-4cf8-a564-8a99f3a78162
-- title:
--   Fibre Regular: is Regular Local Ring stalk quot maximal Ideal
-- statement:
--   The Fibre Regular construction uses the is Regular Local Ring stalk quot maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothFibreRegularLocalRing.lean#L27-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothFibreRegularLocalRing.lean#L27-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothFibreRegularLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.FibreRegular

theorem GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal :
    ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) [Smooth π] (y : Y),
      IsRegularLocalRing (Y.presheaf.stalk y ⧸
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (π y))).map (π.stalkMap y).hom) := by sorry
