-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_flRow_intInd
-- name    : GlobalTheory.LocFlat.UnramFlat.flRow_intInd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:04.57481+00:00
-- url     : https://prove2.me/theorems/9010d59b-41d9-4e26-9b1c-95563d0c9105
-- title:
--   Unram Flat: fl Row int Ind
-- statement:
--   The Unram Flat construction uses the fl Row int Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L126-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L126-L148

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
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem GlobalTheory.LocFlat.UnramFlat.flRow_intInd {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (p : ℕ)
    (hp1 : 1 ≤ p) (hpc : p ≤ c) :
    flRow ψ ν p (Set.indicator {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) =
      Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1 := by sorry
