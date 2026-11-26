-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_c_mem
-- name    : GlobalTheory.UnitLemma.c_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:21.626466+00:00
-- url     : https://prove2.me/theorems/1cdc3b77-9b46-42a4-a324-b1a8a3035676
-- title:
--   Unit Lemma: c mem
-- statement:
--   The Unit Lemma construction uses the c mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NLineOne.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NLineOne.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInhabitants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NLineOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial IsLocalRing

theorem GlobalTheory.UnitLemma.c_mem (K : UQ) {z : K.E} (hz : z ∈ (algebraMap K.O K.E).range) : K.c z ∈ (algebraMap K.O K.E).range := by sorry
