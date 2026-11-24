-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_OpELevi_opE_const_mul
-- name    : GlobalTheory.RootEx.OpELevi.opE_const_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:00.403814+00:00
-- url     : https://prove2.me/theorems/5a47dc6b-fd98-4064-b8f3-30d85a3730c2
-- title:
--   Op ELevi: op E const mul
-- statement:
--   The Op ELevi construction uses the op E const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L260-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L260-L265

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
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
omit [DecidableEq n] [DecidableEq n'] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [BorelSpace k]

theorem GlobalTheory.RootEx.OpELevi.opE_const_mul (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k) (a : ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun x => a * Φ x) x₀ = a * opE ψ ν p Φ x₀ := by sorry
