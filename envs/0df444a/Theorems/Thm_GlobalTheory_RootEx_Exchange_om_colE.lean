-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Exchange_om_colE
-- name    : GlobalTheory.RootEx.Exchange.om_colE
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:52.87581+00:00
-- url     : https://prove2.me/theorems/0283a9fa-9c19-4305-95a7-8793eaae518c
-- title:
--   Exchange: om col E
-- statement:
--   The Exchange construction uses the om col E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L237-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L237-L242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem GlobalTheory.RootEx.Exchange.om_colE (μ : kˣ →* ℂˣ) (p : ℕ) (β : n → k) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    om μ 1 (colE c p β) Φ x = Φ (((colE c p β)⁻¹ : GL (n ⊕ Fin c) k).val * x) := by sorry
