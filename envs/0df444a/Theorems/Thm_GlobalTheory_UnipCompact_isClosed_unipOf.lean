-- Prove2me | Theorems.Thm_GlobalTheory_UnipCompact_isClosed_unipOf
-- name    : GlobalTheory.UnipCompact.isClosed_unipOf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:02:20.319053+00:00
-- url     : https://prove2.me/theorems/57273dcd-dfa4-4cdb-983c-a177162b616e
-- title:
--   Unip Compact: is Closed unip Of
-- statement:
--   The Unip Compact construction uses the is Closed unip Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsCompactSubgroup.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsCompactSubgroup.lean#L19-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsCompactSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open GlobalTheory GlobalTheory.UnipCompact
variable {n : Type}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Fintype n] [DecidableEq n]

theorem GlobalTheory.UnipCompact.isClosed_unipOf (c : n → ℤ) : IsClosed (unipOf k c : Set (GL n k)) := by sorry
