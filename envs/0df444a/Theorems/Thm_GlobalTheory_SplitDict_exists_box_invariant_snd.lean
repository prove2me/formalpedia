-- Prove2me | Theorems.Thm_GlobalTheory_SplitDict_exists_box_invariant_snd
-- name    : GlobalTheory.SplitDict.exists_box_invariant_snd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:04:17.14519+00:00
-- url     : https://prove2.me/theorems/9f842072-4eef-43ab-a2c4-08ce259869c5
-- title:
--   Split Dict: exists box invariant snd
-- statement:
--   The Split Dict construction uses the exists box invariant snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L30-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L30-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}
omit [DecidableEq n] [T2Space T]

theorem GlobalTheory.SplitDict.exists_box_invariant_snd {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) :
    ∃ s : kˣ, ∀ u ∈ box n s, ∀ z : T × (n → k), f (z.1, z.2 + u) = f z := by sorry
