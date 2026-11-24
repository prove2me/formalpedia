-- Prove2me | Theorems.Thm_GlobalTheory_JR_DeltaLift_full_mulVec_cs
-- name    : GlobalTheory.JR.DeltaLift.full_mulVec_cs
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:25:29.920029+00:00
-- url     : https://prove2.me/theorems/dadaffad-c8f2-4cc8-b20c-e9d86627aad9
-- title:
--   Delta Lift: full mul Vec cs
-- statement:
--   The Delta Lift construction uses the full mul Vec cs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisHankelDetNeZeroOfLift.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisHankelDetNeZeroOfLift.lean#L21-L24

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

theorem GlobalTheory.JR.DeltaLift.full_mulVec_cs (Z : Gl r k) (V : Fin (r + 1) → k) (i : Fin r) :
    (full Z *ᵥ V) (Fin.castSucc i) = (Z.1 *ᵥ (fun j => V (Fin.castSucc j))) i + V (Fin.last r) * Z.2.1 i := by sorry
