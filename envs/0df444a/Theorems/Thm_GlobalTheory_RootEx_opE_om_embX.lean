-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_opE_om_embX
-- name    : GlobalTheory.RootEx.opE_om_embX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:14.581256+00:00
-- url     : https://prove2.me/theorems/cf30394f-60e3-49fe-afc0-2d27fb1f7a07
-- title:
--   Root Ex: op E om emb X
-- statement:
--   The Root Ex construction uses the op E om emb X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L273-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L273-L317

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
open GlobalTheory.RootEx.OpELevi

theorem GlobalTheory.RootEx.opE_om_embX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), (∀ g : GL n k, opE ψ ν p (om μ 1 (embX c g) Φ) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) • om μ 1 g (opE ψ ν p Φ)) ∧ ∀ g : GL n' k, opE ψ ν p (om μ (embX (c + 1) g) 1 Φ) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - p) : ℝ) : ℂ) • om μ g 1 (opE ψ ν p Φ) := by sorry
