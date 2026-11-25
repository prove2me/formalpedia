-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_UnifChange_inv_sub_inv_mem
-- name    : GlobalTheory.SymChain.UnifChange.inv_sub_inv_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:01.636078+00:00
-- url     : https://prove2.me/theorems/1a4d2339-b5ad-5cdb-9c4f-d56423fb0869
-- title:
--   Unif Change: inv sub inv mem
-- statement:
--   The Unif Change construction uses the inv sub inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSymDataOfUnifCongr.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSymDataOfUnifCongr.lean#L119-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSymDataOfUnifCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymChain
open GlobalTheory.SymChain.UnifChange
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
variable {ϖ ϖ' : kˣ}

theorem GlobalTheory.SymChain.UnifChange.inv_sub_inv_mem (hϖ : IsUnif ϖ) (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) ≤ 1 := by sorry
