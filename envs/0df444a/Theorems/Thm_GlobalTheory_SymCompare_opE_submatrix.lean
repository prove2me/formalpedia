-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_opE_submatrix
-- name    : GlobalTheory.SymCompare.opE_submatrix
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:35.511353+00:00
-- url     : https://prove2.me/theorems/3ed92603-69dd-4319-a3e1-a708127aef33
-- title:
--   Sym Compare: op E submatrix
-- statement:
--   The Sym Compare construction uses the op E submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L106-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L106-L131

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
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}
omit [DecidableEq n] [DecidableEq m] [DecidableEq n'] [DecidableEq m']

theorem GlobalTheory.SymCompare.opE_submatrix [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (p : ℕ) (e : n ≃ m) (e' : n' ≃ m') (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix m m' k) :
    opE ψ ν p (fun x => Φ (x.submatrix (sE e c) (sE e' (c + 1)))) x₀ = opE ψ ν p Φ (x₀.submatrix e e') := by sorry
