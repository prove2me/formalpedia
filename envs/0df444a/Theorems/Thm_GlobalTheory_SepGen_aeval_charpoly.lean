-- Prove2me | Theorems.Thm_GlobalTheory_SepGen_aeval_charpoly
-- name    : GlobalTheory.SepGen.aeval_charpoly
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:53:14.696647+00:00
-- url     : https://prove2.me/theorems/dc6534c7-d72a-465b-8f80-b005d01e0f63
-- title:
--   Sep Gen: aeval charpoly
-- statement:
--   The Sep Gen construction uses the aeval charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinEqTopAndIsReducedOfCharpolySeparable.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinEqTopAndIsReducedOfCharpolySeparable.lean#L29-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SepGen
variable {E : Type} [Field E] {A : Type} [CommRing A] [Algebra E A] [Module.Finite E A]

theorem GlobalTheory.SepGen.aeval_charpoly (y : A) : aeval y (LinearMap.mulLeft E y).charpoly = 0 := by sorry
