-- Prove2me | Theorems.Thm_GlobalTheory_JR_DeltaLift_vecMul_full_cs
-- name    : GlobalTheory.JR.DeltaLift.vecMul_full_cs
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:25:31.433471+00:00
-- url     : https://prove2.me/theorems/84ee2418-5b53-44a7-a8c0-f7650f726395
-- title:
--   Delta Lift: vec Mul full cs
-- statement:
--   The Delta Lift construction uses the vec Mul full cs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisHankelDetNeZeroOfLift.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisHankelDetNeZeroOfLift.lean#L26-L28

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

theorem GlobalTheory.JR.DeltaLift.vecMul_full_cs (Z : Gl r k) (V : Fin (r + 1) → k) (j : Fin r) :
    (V ᵥ* full Z) (Fin.castSucc j) = ((fun i => V (Fin.castSucc i)) ᵥ* Z.1) j + V (Fin.last r) * Z.2.2.1 j := by sorry
