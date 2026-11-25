-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_flat_contr_intIndicator
-- name    : GlobalTheory.LocFlat.flat_contr_intIndicator
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:54.747172+00:00
-- url     : https://prove2.me/theorems/ed8de407-7da5-41da-a613-fca33499f08e
-- title:
--   Loc Flat: flat contr int Indicator
-- statement:
--   The Loc Flat construction uses the flat contr int Indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L273-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L273-L275

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
open GlobalTheory.LocFlat.UnramFlat

theorem GlobalTheory.LocFlat.flat_contr_intIndicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), HasConductor ψ 1 → IsUnitVol ν → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (c p : ℕ), GlobalTheory.LocFlat.flCol ψ ν p (Set.indicator {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) = (if p = 0 ∨ c + 1 < p then fun x => Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁ else Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) ∧ (1 ≤ p → p ≤ c → GlobalTheory.LocFlat.flRow ψ ν p (Set.indicator {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) ∧ ∀ q, GlobalTheory.LocFlat.contr ψ ν (Set.indicator {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) (Set.indicator {x : Matrix (n'' ⊕ Unit) n k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) q = Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.1 * Set.indicator {x : Matrix n'' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.2 := by sorry
