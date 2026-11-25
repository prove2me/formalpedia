-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_mul
-- name    : GlobalTheory.RootEx.OpELevi.nabs_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:37.382207+00:00
-- url     : https://prove2.me/theorems/ac4ddfb1-419d-5bdd-8e70-3d0cf3aa4a90
-- title:
--   Op ELevi: nabs mul
-- statement:
--   The Op ELevi construction uses the nabs mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul

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

theorem GlobalTheory.RootEx.OpELevi.nabs_mul (x y : kˣ) : nabs k (x * y) = nabs k x * nabs k y := by sorry
