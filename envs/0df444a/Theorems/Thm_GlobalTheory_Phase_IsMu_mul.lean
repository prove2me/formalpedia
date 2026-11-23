-- Prove2me | Theorems.Thm_GlobalTheory_Phase_IsMu_mul
-- name    : GlobalTheory.Phase.IsMu.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:38.834793+00:00
-- url     : https://prove2.me/theorems/85dd6b23-8b4e-41ad-b38c-7dfe86524c02
-- title:
--   Is Mu: mul
-- statement:
--   The Is Mu construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IntMIffInt.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IntMIffInt.lean#L57-L62

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

theorem GlobalTheory.Phase.IsMu.mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by sorry
