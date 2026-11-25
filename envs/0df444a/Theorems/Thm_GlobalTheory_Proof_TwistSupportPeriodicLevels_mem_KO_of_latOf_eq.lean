-- Prove2me | Theorems.Thm_GlobalTheory_Proof_TwistSupportPeriodicLevels_mem_KO_of_latOf_eq
-- name    : GlobalTheory.Proof.TwistSupportPeriodicLevels.mem_KO_of_latOf_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:47:07.907283+00:00
-- url     : https://prove2.me/theorems/38c0c0f3-6c7d-492c-8fbf-8b415b9437b5
-- title:
--   Twist Support Periodic Levels: mem KO of lat Of eq
-- statement:
--   The Twist Support Periodic Levels construction uses the mem KO of lat Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TwistSupportPeriodicLevels.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TwistSupportPeriodicLevels.lean#L11-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.TwistSupportPeriodicLevels
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.Proof.TwistSupportPeriodicLevels.mem_KO_of_latOf_eq {Y : Type} [Fintype Y] [DecidableEq Y] {g : GL Y k} (h : latOf g = latOf 1) :
    g ∈ KO k Y := by sorry
