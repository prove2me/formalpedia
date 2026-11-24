-- Prove2me | Theorems.Thm_GlobalTheory_formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top
-- name    : GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:58.874578+00:00
-- url     : https://prove2.me/theorems/bda566b3-c12f-42a0-8fa7-5611d867b901
-- title:
--   Global Theory: formally Unramified ring Of Integers iff different Ideal eq top
-- statement:
--   The Global Theory construction uses the formally Unramified ring Of Integers iff different Ideal eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FormallyUnramifiedRingOfIntegersIffDifferentIdea.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FormallyUnramifiedRingOfIntegersIffDifferentIdea.lean#L8-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FormallyUnramifiedRingOfIntegersIffDifferentIdea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open NumberField

theorem GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top (F E : Type) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ↔ differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by sorry
