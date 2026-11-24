-- Prove2me | Theorems.Thm_GlobalTheory_UnipCompact_eventually_mem_grp
-- name    : GlobalTheory.UnipCompact.eventually_mem_grp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:02:30.015617+00:00
-- url     : https://prove2.me/theorems/71dbb6e9-6bc0-4d61-97b9-28bb636810ce
-- title:
--   Unip Compact: eventually mem grp
-- statement:
--   The Unip Compact construction uses the eventually mem grp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsCompactSubgroup.lean#L29-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsCompactSubgroup.lean#L29-L46

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

theorem GlobalTheory.UnipCompact.eventually_mem_grp {c : n → ℤ} {u : GL n k} (hu : u ∈ unipOf k c) :
    ∀ᶠ m : ℕ in Filter.atTop, u ∈ GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) := by sorry
