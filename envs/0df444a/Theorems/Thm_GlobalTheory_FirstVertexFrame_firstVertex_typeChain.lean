-- Prove2me | Theorems.Thm_GlobalTheory_FirstVertexFrame_firstVertex_typeChain
-- name    : GlobalTheory.FirstVertexFrame.firstVertex_typeChain
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:58.761036+00:00
-- url     : https://prove2.me/theorems/de342559-ad33-4c87-a208-39572d7add6b
-- title:
--   First Vertex Frame: first Vertex type Chain
-- statement:
--   The First Vertex Frame construction uses the first Vertex type Chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexIteratedLevelChainInFrame.lean#L228-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexIteratedLevelChainInFrame.lean#L228-L318

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexIteratedLevelChainInFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.FirstVertexFrame
open MeasureTheory ValuativeRel Matrix Topology

theorem GlobalTheory.FirstVertexFrame.firstVertex_typeChain : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (s : ℕ) (t : Type) [Fintype t] [DecidableEq t]
    (κ : ℕ) (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin (s + 1))),
    ((∀ u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) (s + 1) 1, ∀ γ : GL (Fin κ) k,
        u * _root_.GlobalTheory.RootEx.embX (s + 1) γ ∈ P.J →
          ∃ gb, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip Fin.val gb.val) ∧
      (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb →
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip Fin.val gb.val →
          ∃ hm : _root_.GlobalTheory.RootEx.embX (s + 1) γ ∈ P.J,
            (P.lam ⟨_, hm⟩ : ℂ) =
              ψ ((ϖ⁻¹ : kˣ) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val γ.val)) ∧
      ∀ u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) (s + 1) 1,
        ∀ hm : u ∈ P.J,
          (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * _root_.GlobalTheory.RootEx.simpleSum u)) →
    ∀ (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, _root_.GlobalTheory.SplitWeil.IsTame (μ j)) (c : ℕ) (H : 0 + c = s + 1),
      (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp
          ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J 1) :
          Set (GL (_root_.GlobalTheory.StepData.XIx (Fin κ) t 0) k)) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.colGroup k κ t ∧
      (∀ γ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.colGroup k κ t, ∃ hm : _root_.GlobalTheory.RootEx.embX c γ ∈
          ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J,
        (((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨_, hm⟩ : ℂ) =
          _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.colChar ψ ϖ γ) ∧
      ∀ u ∈ _root_.GlobalTheory.RootEx.N k (_root_.GlobalTheory.StepData.XIx (Fin κ) t 0) c 1,
        ∀ hm : u ∈ ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J,
          (((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨u, hm⟩ : ℂ) =
            ψ (_root_.GlobalTheory.RootEx.simpleSum u) := by sorry
