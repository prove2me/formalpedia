-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_flCol_eq_integral
-- name    : GlobalTheory.LocFlat.flCol_eq_integral
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:58.50178+00:00
-- url     : https://prove2.me/theorems/697ba44e-1a65-4944-8b7f-e3020ddf3c85
-- title:
--   Loc Flat: fl Col eq integral
-- statement:
--   The Loc Flat construction uses the fl Col eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L415-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L415-L418

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
open Classical

theorem GlobalTheory.LocFlat.flCol_eq_integral (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) :
    flCol ψ ν p Φ = fun x => ∫ e, Φ (ptCol p x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ)
      ∂(Measure.pi fun _ => ν) := by sorry
