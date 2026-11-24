-- Prove2me | Theorems.Thm_GlobalTheory_UnipCompact_exists_compact_subgroup
-- name    : GlobalTheory.UnipCompact.exists_compact_subgroup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:00:18.813429+00:00
-- url     : https://prove2.me/theorems/ee1fa685-527d-42db-b441-f9a2431b22c2
-- title:
--   Unip Compact: exists compact subgroup
-- statement:
--   The Unip Compact construction uses the exists compact subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsCompactSubgroup.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsCompactSubgroup.lean#L48-L56

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

theorem GlobalTheory.UnipCompact.exists_compact_subgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : n → ℤ) (S : Finset (GL n k))
    (hS : ∀ u ∈ S, u ∈ unipOf k c) :
    ∃ H : Subgroup (GL n k), H ≤ unipOf k c ∧ IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by sorry
