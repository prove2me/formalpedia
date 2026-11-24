-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenClosedSequences_resFilt_surjective
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.resFilt_surjective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:33.193907+00:00
-- url     : https://prove2.me/theorems/df7a9a59-fb5b-428c-a11a-5c30d09efdd8
-- title:
--   Open Closed Sequences: res Filt surjective
-- statement:
--   The Open Closed Sequences construction uses the res Filt surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RankFiltrationExists.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RankFiltrationExists.lean#L78-L83

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.resFilt_surjective (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n)
    (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m) : Function.Surjective (resFilt (a := a) (b := b) μ hmn hs) := by sorry
