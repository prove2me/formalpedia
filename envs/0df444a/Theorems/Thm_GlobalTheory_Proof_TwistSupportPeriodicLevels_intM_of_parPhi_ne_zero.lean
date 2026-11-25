-- Prove2me | Theorems.Thm_GlobalTheory_Proof_TwistSupportPeriodicLevels_intM_of_parPhi_ne_zero
-- name    : GlobalTheory.Proof.TwistSupportPeriodicLevels.intM_of_parPhi_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:25.091495+00:00
-- url     : https://prove2.me/theorems/5cb32b81-0745-5370-ba32-16701e10068c
-- title:
--   Twist Support Periodic Levels: int M of par Phi ne zero
-- statement:
--   The Twist Support Periodic Levels construction uses the int M of par Phi ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TwistSupportPeriodicLevels.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TwistSupportPeriodicLevels.lean#L20-L25

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

theorem GlobalTheory.Proof.TwistSupportPeriodicLevels.intM_of_parPhi_ne_zero (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} (hx : parPhi δ x ≠ 0) : IntM x := by sorry
