-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_opE_cut_om_equivariant
-- name    : GlobalTheory.RootEx.opE_cut_om_equivariant
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:36.949373+00:00
-- url     : https://prove2.me/theorems/94863434-052e-407d-be18-0dd84d305100
-- title:
--   Root Ex: op E cut om equivariant
-- statement:
--   The Root Ex construction uses the op E cut om equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OpECutOmEquivariant.lean#L20-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OpECutOmEquivariant.lean#L20-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpECutOmEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open MeasureTheory ValuativeRel Matrix

theorem GlobalTheory.RootEx.opE_cut_om_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (χ : (n' → k) → ℂ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : GL n k), ∀ u ∈ _root_.GlobalTheory.RootEx.N k n c p ⊓ _root_.GlobalTheory.RootEx.N k n c (p + 1), _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0) * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x * u) Φ y) = (((_root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((p + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * (ψ (-_root_.GlobalTheory.RootEx.simpleSum u) : ℂ)) • _root_.GlobalTheory.SplitWeil.om μ 1 x (_root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0) * Φ y)) := by sorry
