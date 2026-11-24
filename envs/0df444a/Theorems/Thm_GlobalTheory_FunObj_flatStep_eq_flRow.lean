-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_flatStep_eq_flRow
-- name    : GlobalTheory.FunObj.flatStep_eq_flRow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:35:25.360037+00:00
-- url     : https://prove2.me/theorems/7f653992-f4ce-40b7-9e2e-60e9925a375d
-- title:
--   Fun Obj: flat Step eq fl Row
-- statement:
--   The Fun Obj construction uses the flat Step eq fl Row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L88-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
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
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar k Circle) (ν : Measure k)

theorem GlobalTheory.FunObj.flatStep_eq_flRow (hc : Odd c) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (w : KeptVar n c n' → k) :
    flatStep ψ ν Φ x₀ w = flRow ψ ν (c / 2 + 1) Φ (fromRows x₀ (Matrix.of fun _ s => w (rowIx hc s))) := by sorry
