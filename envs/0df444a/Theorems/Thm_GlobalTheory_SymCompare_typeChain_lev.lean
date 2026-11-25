-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_typeChain_lev
-- name    : GlobalTheory.SymCompare.typeChain_lev
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:00.959394+00:00
-- url     : https://prove2.me/theorems/96c9d61b-19d7-54ec-9e61-3a968e2ef621
-- title:
--   Sym Compare: type Chain lev
-- statement:
--   The Sym Compare construction uses the type Chain lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L240-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L240-L251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
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
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t t' : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype t'] [DecidableEq t']
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {s : ℕ}

theorem GlobalTheory.SymCompare.typeChain_lev (f : t ≃ t') (ϖ : kˣ) (P : TypeDatum k (κ ⊕ Fin (s + 1))) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j c : ℕ) (h : j + c = s + 1) (g : GL (XIx κ t j ⊕ Fin c) k) :
    reGL (sE (eI (κ ⊕ Fin j) f j) c) g ∈ ((typeChain t' ϖ P μ hμ).lev j c h).J ↔
      g ∈ ((typeChain t ϖ P μ hμ).lev j c h).J := by sorry
