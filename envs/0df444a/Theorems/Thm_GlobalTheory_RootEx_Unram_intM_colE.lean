-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Unram_intM_colE
-- name    : GlobalTheory.RootEx.Unram.intM_colE
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:29:37.580323+00:00
-- url     : https://prove2.me/theorems/d69fd7ab-4351-4566-998a-16fa27046243
-- title:
--   Unram: int M col E
-- statement:
--   The Unram construction uses the int M col E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L196-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L196-L225

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
omit [Fintype n'] [DecidableEq n']

theorem GlobalTheory.RootEx.Unram.intM_colE {p : ℕ} (hp : p + 1 ≤ c) (β : n → k) (x₀ : Matrix n n' k) (e) :
    IntM (((colE c (p + 1) β)⁻¹).val * affPt (c := c) (p + 1) x₀ e) ↔
      IntM (affPt (c := c) (p + 1) x₀ e) ∧ ∀ r, β r ∈ 𝒪[k] := by sorry
