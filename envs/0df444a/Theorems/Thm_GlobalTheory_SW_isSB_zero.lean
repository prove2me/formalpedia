-- Prove2me | Theorems.Thm_GlobalTheory_SW_isSB_zero
-- name    : GlobalTheory.SW.isSB_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:35.95627+00:00
-- url     : https://prove2.me/theorems/a111f617-04d0-4743-835e-579a5a0c6173
-- title:
--   SW: is SB zero
-- statement:
--   The SW construction uses the is SB zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IMemSiegel.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IMemSiegel.lean#L34-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.isSB_zero : IsSB (0 : Matrix κ ι K → ℂ) := by sorry
