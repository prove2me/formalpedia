-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenClosedSequences_resFilt_apply
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.resFilt_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:08:59.6408+00:00
-- url     : https://prove2.me/theorems/cc49039f-626d-4010-9915-b87f2f51609f
-- title:
--   Open Closed Sequences: res Filt apply
-- statement:
--   The Open Closed Sequences construction uses the res Filt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RankFiltrationExists.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RankFiltrationExists.lean#L74-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenSetOfLeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RankFiltrationExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.resFilt_apply (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n) (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m)
    (Φ : (filt a b μ (Set.Iio n) κ).toSubmodule) (x : RankIn k a b s) :
    (resFilt μ hmn hs Φ).1 x = Φ.1.1 ⟨x.1, ((hs _).1 x.2).2.trans_le hmn⟩ := by sorry
