-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_phase_eq
-- name    : GlobalTheory.FunObj.phase_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:05:22.940922+00:00
-- url     : https://prove2.me/theorems/8602cdc3-6f7f-4c2d-9a01-dfcb726e5672
-- title:
--   Fun Obj: phase eq
-- statement:
--   The Fun Obj construction uses the phase eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L208-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L208-L221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}

theorem GlobalTheory.FunObj.phase_eq (x : ColArgs G) (e : Vars G) :
    phase x e = ∑ j : Fin (G.m - 1), ch (stepPt (x j) (e j)) + pairPhase x fun j => keptPart (e j) := by sorry
