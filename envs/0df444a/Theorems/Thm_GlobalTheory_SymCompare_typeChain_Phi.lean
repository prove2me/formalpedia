-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_typeChain_Phi
-- name    : GlobalTheory.SymCompare.typeChain_Phi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:23.261454+00:00
-- url     : https://prove2.me/theorems/1824c4ac-ee03-4386-ab62-9c8ba30e1e41
-- title:
--   Sym Compare: type Chain Phi
-- statement:
--   The Sym Compare construction uses the type Chain Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L253-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L253-L263

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

theorem GlobalTheory.SymCompare.typeChain_Phi (f : t ≃ t') (ϖ : kˣ) (P : TypeDatum k (κ ⊕ Fin (s + 1))) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j c : ℕ) (h : j + c = s) :
    (typeChain t' ϖ P μ hμ).Phi j c h = fun x => (typeChain t ϖ P μ hμ).Phi j c h
      (x.submatrix (sE (eI (κ ⊕ Fin (j + 1)) f (j + 1)) c) (sE (eI (κ ⊕ Fin j) f j) (c + 1))) := by sorry
