-- Prove2me | Theorems.Thm_GlobalTheory_T_flatMaps_preserve_schwartzBruhat_and_surjective
-- name    : GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:46.416697+00:00
-- url     : https://prove2.me/theorems/d022be2e-4514-463c-92fb-539fa45e1c65
-- title:
--   T: flat Maps preserve schwartz Bruhat and surjective
-- statement:
--   The T construction uses the flat Maps preserve schwartz Bruhat and surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjectiveStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjectiveStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → (p ≤ c + 1 → (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flCol ψ ν p Φ ∈ SB _) ∧ ∀ Ψ ∈ SB (Matrix n (n' ⊕ Unit) k), ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flCol ψ ν p Φ = Ψ) ∧ (p ≤ c → (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flRow ψ ν p Φ ∈ SB _) ∧ ∀ Ψ ∈ SB (Matrix (n ⊕ Unit) n' k), ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flRow ψ ν p Φ = Ψ) := by sorry
