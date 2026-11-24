-- Prove2me | Theorems.Thm_GlobalTheory_CosetVolProd_volR_Cgrp
-- name    : GlobalTheory.CosetVolProd.volR_Cgrp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:10:39.165037+00:00
-- url     : https://prove2.me/theorems/38ff4d6e-3ec5-4334-8f70-63483c2613f6
-- title:
--   Coset Vol Prod: vol R Cgrp
-- statement:
--   The Coset Vol Prod construction uses the vol R Cgrp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ParabolicHaarVolumeConjIntersectionEqMul.lean#L14-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ParabolicHaarVolumeConjIntersectionEqMul.lean#L14-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParabolicHaarVolumeConjIntersectionEqMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.CosetVolProd
open MeasureTheory ValuativeRel Matrix Topology

theorem GlobalTheory.CosetVolProd.volR_Cgrp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k), IsOpen (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h) : Set (GL n k)) → ∀ m : Measure (GL n k), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.volR ν m (_root_.GlobalTheory.StepData.Cgrp J h) = _root_.GlobalTheory.RootEx.volN ν n c 1 ((_root_.GlobalTheory.StepData.Cgrp J h).subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1)) * m (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h)) := by sorry
