-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenClosedSequences_exists_extend_rankIn
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.exists_extend_rankIn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:26.102546+00:00
-- url     : https://prove2.me/theorems/6b1aba66-71f9-4df0-b796-c1f74690163e
-- title:
--   Open Closed Sequences: exists extend rank In
-- statement:
--   The Open Closed Sequences construction uses the exists extend rank In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RankFiltrationExists.lean#L45-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RankFiltrationExists.lean#L45-L60

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
omit [DecidableEq a] [DecidableEq b]

theorem GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.exists_extend_rankIn {s : Set ℕ} {κ n : ℕ} (hs : ∀ r ∈ s, κ ≤ r ∧ r < n) (f : SB (RankIn k a b s)) :
    ∃ F : SB (RankIn k a b (Set.Iio n)), (∀ x : RankIn k a b (Set.Iio n), x.1.rank < κ → F.1 x = 0) ∧
      ∀ x : RankIn k a b s, F.1 ⟨x.1, (hs _ x.2).2⟩ = f.1 x := by sorry
