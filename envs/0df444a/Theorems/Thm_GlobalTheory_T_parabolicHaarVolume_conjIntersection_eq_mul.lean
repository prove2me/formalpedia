-- Prove2me | Theorems.Thm_GlobalTheory_T_parabolicHaarVolume_conjIntersection_eq_mul
-- name    : GlobalTheory.T.parabolicHaarVolume_conjIntersection_eq_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:19:47.325444+00:00
-- url     : https://prove2.me/theorems/6151951c-5d8b-4465-8c65-8e385af7974d
-- title:
--   T: parabolic Haar Volume conj Intersection eq mul
-- statement:
--   The T construction uses the parabolic Haar Volume conj Intersection eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ParabolicHaarVolumeConjIntersectionEqMulStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ParabolicHaarVolumeConjIntersectionEqMulStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParabolicHaarVolumeConjIntersectionEqMul
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParabolicHaarVolumeConjIntersectionEqMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.parabolicHaarVolume_conjIntersection_eq_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k), IsOpen (prX (Cgrp J h) : Set (GL n k)) → ∀ m : Measure (GL n k), volR ν m (Cgrp J h) = volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) * m (prX (Cgrp J h)) := by sorry
