-- Prove2me | Theorems.Thm_GlobalTheory_Phase_Ph_mul
-- name    : GlobalTheory.Phase.Ph.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:54.519994+00:00
-- url     : https://prove2.me/theorems/7eb4acd2-e157-414b-a91c-8f08b1d604f6
-- title:
--   Ph: mul
-- statement:
--   The Ph construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IntMIffInt.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IntMIffInt.lean#L78-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open GlobalTheory.SW
open GlobalTheory GlobalTheory.Phase
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
variable {n g : ℕ}

theorem GlobalTheory.Phase.Ph.mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by sorry
