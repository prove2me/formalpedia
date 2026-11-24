-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_coords_submatrix
-- name    : GlobalTheory.SymCompare.coords_submatrix
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:18:03.294592+00:00
-- url     : https://prove2.me/theorems/731b0f47-5ca5-43a9-b479-f7abf75bf5c5
-- title:
--   Sym Compare: coords submatrix
-- statement:
--   The Sym Compare construction uses the coords submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L75-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L75-L87

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
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}

theorem GlobalTheory.SymCompare.coords_submatrix {ι ι' κ κ' : Type*}
    (F : LatFrame k ι n) (F' : LatFrame k ι' m) (a : ι ≃ ι') (b : n ≃ m) (ho : a.trans F'.ord = F.ord.trans b)
    (hb : F'.bas = reGL b F.bas)
    (G : LatFrame k κ n') (G' : LatFrame k κ' m') (a' : κ ≃ κ') (b' : n' ≃ m') (ho' : a'.trans G'.ord = G.ord.trans b')
    (hb' : G'.bas = reGL b' G.bas) (x : Matrix m m' k) :
    (F'.coords G' x).submatrix a a' = F.coords G (x.submatrix b b') := by sorry
