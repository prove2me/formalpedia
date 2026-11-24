-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Unram_intM_affPt
-- name    : GlobalTheory.RootEx.Unram.intM_affPt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:38.58901+00:00
-- url     : https://prove2.me/theorems/ff11157d-9514-405a-a8c4-cace7e53cc5b
-- title:
--   Unram: int M aff Pt
-- statement:
--   The Unram construction uses the int M aff Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L176-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L176-L193

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open MeasureTheory ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n']

theorem GlobalTheory.RootEx.Unram.intM_affPt {p : ℕ} (x₀ : Matrix n n' k) (e) :
    _root_.GlobalTheory.StepData.IntM (_root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e) ↔
      _root_.GlobalTheory.StepData.IntM x₀ ∧ ∀ rs, e rs ∈ 𝒪[k] := by sorry
