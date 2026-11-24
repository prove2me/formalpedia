-- Prove2me | Theorems.Thm_GlobalTheory_StepData_blockGL_mem_KO
-- name    : GlobalTheory.StepData.blockGL_mem_KO
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:22:12.903794+00:00
-- url     : https://prove2.me/theorems/5472f965-1d80-454d-9a14-4b0f51a837b7
-- title:
--   Step Data: block GL mem KO
-- statement:
--   The Step Data construction uses the block GL mem KO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L166-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L166-L171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.blockGL_mem_KO {g : GL a k} {B : Matrix a t k} {D : GL t k} (hg : g ∈ KO k a) (hB : IntM B)
    (hD : D ∈ KO k t) : blockGL g B D ∈ KO k (a ⊕ t) := by sorry
