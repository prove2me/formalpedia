-- Prove2me | Theorems.Thm_GlobalTheory_JR_DeltaLift_full_cc
-- name    : GlobalTheory.JR.DeltaLift.full_cc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:17.922948+00:00
-- url     : https://prove2.me/theorems/f0f3ae82-9889-4360-9f48-78bda35a7365
-- title:
--   Delta Lift: full cc
-- statement:
--   The Delta Lift construction uses the full cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisHankelDetNeZeroOfLift.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisHankelDetNeZeroOfLift.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DeltaLift
variable {k : Type} [Field k] {r : ℕ}

theorem GlobalTheory.JR.DeltaLift.full_cc (Z : Gl r k) (i j : Fin r) : full Z (Fin.castSucc i) (Fin.castSucc j) = Z.1 i j := by sorry
