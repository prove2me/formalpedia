-- Prove2me | Theorems.Thm_GlobalTheory_Proof_TwistSupportPeriodicLevels_intM_of_coords
-- name    : GlobalTheory.Proof.TwistSupportPeriodicLevels.intM_of_coords
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:47:00.40013+00:00
-- url     : https://prove2.me/theorems/e89b7bc2-d5b8-4159-99f5-75402932d05f
-- title:
--   Twist Support Periodic Levels: int M of coords
-- statement:
--   The Twist Support Periodic Levels construction uses the int M of coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TwistSupportPeriodicLevels.lean#L63-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TwistSupportPeriodicLevels.lean#L63-L73

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
variable {r s s' : Type} [Fintype r] [DecidableEq r]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']

theorem GlobalTheory.Proof.TwistSupportPeriodicLevels.intM_of_coords {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {x : Matrix Y Y' k} (h : IntM (F.coords F' x)) : IntM x := by sorry
