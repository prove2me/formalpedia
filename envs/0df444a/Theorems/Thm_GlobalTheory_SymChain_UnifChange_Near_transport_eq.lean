-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_UnifChange_Near_transport_eq
-- name    : GlobalTheory.SymChain.UnifChange.Near.transport_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:30:24.334962+00:00
-- url     : https://prove2.me/theorems/012b3beb-dce5-4264-ada3-e331c491dd2c
-- title:
--   Near: transport eq
-- statement:
--   The Near construction uses the transport eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSymDataOfUnifCongr.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSymDataOfUnifCongr.lean#L63-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSymDataOfUnifCongr
import Theorems.Thm_GlobalTheory_StepData_HasTypes_transport

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

theorem GlobalTheory.SymChain.UnifChange.Near.transport_eq {F G : LatFrame k ι Y} {F' G' : LatFrame k ι' Y'} (h : Near F G) (h' : Near F' G')
    {f : Matrix ι ι' k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x) (hp : ∀ x y, MaxM y → f (x + y) = f x) :
    G.transport G' f = F.transport F' f := by sorry
