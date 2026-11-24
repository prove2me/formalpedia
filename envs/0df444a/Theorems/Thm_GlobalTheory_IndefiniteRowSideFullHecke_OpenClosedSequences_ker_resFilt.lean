-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenClosedSequences_ker_resFilt
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.ker_resFilt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:54.881557+00:00
-- url     : https://prove2.me/theorems/d115d348-a34c-439e-93e4-3f91a4acf01a
-- title:
--   Open Closed Sequences: ker res Filt
-- statement:
--   The Open Closed Sequences construction uses the ker res Filt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RankFiltrationExists.lean#L85-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RankFiltrationExists.lean#L85-L94

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.ker_resFilt (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n)
    (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m) (Φ : (filt a b μ (Set.Iio n) κ).toSubmodule) :
    resFilt μ hmn hs Φ = 0 ↔ Φ.1 ∈ (filt a b μ (Set.Iio n) m).toSubmodule := by sorry
