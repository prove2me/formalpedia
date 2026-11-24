-- Prove2me | Theorems.Thm_GlobalTheory_SplitDict_pf_bijOn
-- name    : GlobalTheory.SplitDict.pf_bijOn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:04.439241+00:00
-- url     : https://prove2.me/theorems/55ba51b9-3ef6-4699-a2c4-805e12fc7595
-- title:
--   Split Dict: pf bij On
-- statement:
--   The Split Dict construction uses the pf bij On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L165-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L165-L197

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
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitDict.pf_bijOn (m : Measure k) [m.IsAddHaarMeasure] (h : HasConductor ψ c) :
    Set.BijOn (pf ψ (Measure.pi fun _ => m)) {f | f ∈ SB (T × (n → k))} {f | f ∈ SB (T × (n → k))} := by sorry
