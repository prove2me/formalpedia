-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_prX_inf_eq_iff
-- name    : GlobalTheory.SymCompare.prX_inf_eq_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:20.905809+00:00
-- url     : https://prove2.me/theorems/37a9360e-7a35-466e-a94c-2759907c4c82
-- title:
--   Sym Compare: pr X inf eq iff
-- statement:
--   The Sym Compare construction uses the pr X inf eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L53-L62

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

theorem GlobalTheory.SymCompare.prX_inf_eq_iff (J : Subgroup (GL (n ⊕ Fin c) k)) : prX (R k n c 1 ⊓ J) = J.comap (embX c) ↔
    ∀ u ∈ N k n c 1, ∀ g, u * embX c g ∈ J → embX c g ∈ J := by sorry
