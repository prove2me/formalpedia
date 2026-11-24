-- Prove2me | Theorems.Thm_GlobalTheory_PadicComplexIso_mk_le_continuum_of_denseRange
-- name    : GlobalTheory.PadicComplexIso.mk_le_continuum_of_denseRange
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:33:26.000621+00:00
-- url     : https://prove2.me/theorems/4b0f6cce-8f04-4a0f-b856-96a14322bb56
-- title:
--   Padic Complex Iso: mk le continuum of dense Range
-- statement:
--   The Padic Complex Iso construction uses the mk le continuum of dense Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MkLeContinuumOfDenseRange.lean#L28-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MkLeContinuumOfDenseRange.lean#L28-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MkLeContinuumOfDenseRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open Cardinal
open GlobalTheory GlobalTheory.PadicComplexIso

theorem GlobalTheory.PadicComplexIso.mk_le_continuum_of_denseRange {X Y : Type} [MetricSpace Y] (f : X → Y)
    (hf : DenseRange f) (hX : #X ≤ 𝔠) : #Y ≤ 𝔠 := by sorry
