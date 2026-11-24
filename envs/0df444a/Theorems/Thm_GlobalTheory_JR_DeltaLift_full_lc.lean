-- Prove2me | Theorems.Thm_GlobalTheory_JR_DeltaLift_full_lc
-- name    : GlobalTheory.JR.DeltaLift.full_lc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:24:56.721955+00:00
-- url     : https://prove2.me/theorems/0784b3d7-19b8-4fd5-95d8-3271ad584487
-- title:
--   Delta Lift: full lc
-- statement:
--   The Delta Lift construction uses the full lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisHankelDetNeZeroOfLift.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisHankelDetNeZeroOfLift.lean#L18-L19

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

theorem GlobalTheory.JR.DeltaLift.full_lc (Z : Gl r k) (j : Fin r) : full Z (Fin.last r) (Fin.castSucc j) = Z.2.2.1 j := by sorry
