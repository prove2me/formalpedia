-- Prove2me | Theorems.Thm_GlobalTheory_InertSupp_unipRad_eq_unipOf
-- name    : GlobalTheory.InertSupp.unipRad_eq_unipOf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:51:43.966232+00:00
-- url     : https://prove2.me/theorems/68957501-a04a-42db-8509-fcc5001fecd9
-- title:
--   Inert Supp: unip Rad eq unip Of
-- statement:
--   The Inert Supp construction uses the unip Rad eq unip Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeviEmbMulSingle.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeviEmbMulSingle.lean#L68-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_GodementJacquetZeta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory
open GlobalTheory GlobalTheory.InertSupp
variable {n : Type} [Fintype n] [DecidableEq n]
variable (R : Type) [CommRing R]
variable {R}
variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
open ValuativeRel Matrix MeasureTheory
variable {n : Type} [Fintype n] [DecidableEq n]
variable (R : Type) [CommRing R]
variable {R}
variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)]
variable (R)

theorem GlobalTheory.InertSupp.unipRad_eq_unipOf {e : (Σ a, m a) ≃ n}
    {c : n → ℤ} (h : ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j) :
    _root_.GlobalTheory.SmGL.unipRad R e = _root_.GlobalTheory.InertSupp.unipOf R c := by sorry
