-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Unram_mem_of_psi
-- name    : GlobalTheory.RootEx.Unram.mem_of_psi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:02.9389+00:00
-- url     : https://prove2.me/theorems/6b6cba4c-afa8-4fc5-9964-cda48b30f933
-- title:
--   Unram: mem of psi
-- statement:
--   The Unram construction uses the mem of psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L240-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEmbXMul.lean#L240-L255

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

theorem GlobalTheory.RootEx.Unram.mem_of_psi {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {x : k}
    (hx : ∀ t ∈ 𝒪[k], ψ (t * x) = 1) : x ∈ 𝒪[k] := by sorry
