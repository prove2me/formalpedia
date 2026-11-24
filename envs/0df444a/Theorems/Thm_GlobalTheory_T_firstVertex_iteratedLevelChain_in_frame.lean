-- Prove2me | Theorems.Thm_GlobalTheory_T_firstVertex_iteratedLevelChain_in_frame
-- name    : GlobalTheory.T.firstVertex_iteratedLevelChain_in_frame
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:19:44.947809+00:00
-- url     : https://prove2.me/theorems/f8be00a7-7bd5-42fc-8638-d5238d56401e
-- title:
--   T: first Vertex iterated Level Chain in frame
-- statement:
--   The T construction uses the first Vertex iterated Level Chain in frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexIteratedLevelChainInFrameStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexIteratedLevelChainInFrameStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexIteratedLevelChainInFrame
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexIteratedLevelChainInFrameStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.firstVertex_iteratedLevelChain_in_frame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (s : ℕ) (t : Type) [Fintype t] [DecidableEq t] (κ : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin (s + 1))), ((∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ γ : GL (Fin κ) k, u * embX (s + 1) γ ∈ P.J → ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧ (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb → IsUpperUnip Fin.val gb.val → ∃ hm : embX (s + 1) γ ∈ P.J, (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧ ∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ hm : u ∈ P.J, (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u)) → ∀ (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (c : ℕ) (H : 0 + c = s + 1), (prX (Cgrp ((typeChain t ϖ P μ hμ).lev 0 c H).J 1) : Set (GL (XIx (Fin κ) t 0) k)) = colGroup k κ t ∧ (∀ γ ∈ colGroup k κ t, ∃ hm : embX c γ ∈ ((typeChain t ϖ P μ hμ).lev 0 c H).J, (((typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨_, hm⟩ : ℂ) = colChar ψ ϖ γ) ∧ ∀ u ∈ N k (XIx (Fin κ) t 0) c 1, ∀ hm : u ∈ ((typeChain t ϖ P μ hμ).lev 0 c H).J, (((typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨u, hm⟩ : ℂ) = ψ (simpleSum u) := by sorry
