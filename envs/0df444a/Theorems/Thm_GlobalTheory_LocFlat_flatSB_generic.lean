-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_flatSB_generic
-- name    : GlobalTheory.LocFlat.flatSB_generic
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:27:37.832329+00:00
-- url     : https://prove2.me/theorems/00f04b3e-1d37-4305-ba89-a9d80edda62d
-- title:
--   Loc Flat: flat SB generic
-- statement:
--   The Loc Flat construction uses the flat SB generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L102-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L102-L121

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
open Filter Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open Classical

theorem GlobalTheory.LocFlat.flatSB_generic {X : Type} [TopologicalSpace X] [T2Space X] (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    (A : X → ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hA : Continuous fun q : X × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) => A q.1 q.2)
    (R : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → X) (hR : Continuous R)
    (Q : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hQ : Continuous Q)
    (hRA : ∀ x e, R (A x e) = x) (hQA : ∀ x e, Q (A x e) = freeMat p e)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    (fun x => ∫ e, Φ (A x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB X := by sorry
