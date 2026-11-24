-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_inv
-- name    : GlobalTheory.RootEx.OpELevi.nabs_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:38.58904+00:00
-- url     : https://prove2.me/theorems/b48b0242-5263-4c58-97a5-c580ccc7ee28
-- title:
--   Op ELevi: nabs inv
-- statement:
--   The Op ELevi construction uses the nabs inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L22-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RootEx.OpELevi.nabs_inv (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by sorry
