-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_contr_intInd
-- name    : GlobalTheory.LocFlat.UnramFlat.contr_intInd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:28.23781+00:00
-- url     : https://prove2.me/theorems/33de1752-6a91-42ae-9431-7f730072f899
-- title:
--   Unram Flat: contr int Ind
-- statement:
--   The Unram Flat construction uses the contr int Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L223-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L223-L267

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatContrIntIndicator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option linter.unusedSectionVars false
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n : Type} [Fintype n] [DecidableEq n]
variable {n' n'' : Type} [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']

theorem GlobalTheory.LocFlat.UnramFlat.contr_intInd {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν)
    (q : Matrix n n' k × Matrix n'' n k) :
    contr ψ ν (Set.indicator {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1)
      (Set.indicator {x : Matrix (n'' ⊕ Unit) n k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) q =
    Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.1 *
      Set.indicator {x : Matrix n'' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.2 := by sorry
