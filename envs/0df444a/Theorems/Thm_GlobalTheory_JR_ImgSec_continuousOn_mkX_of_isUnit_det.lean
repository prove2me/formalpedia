-- Prove2me | Theorems.Thm_GlobalTheory_JR_ImgSec_continuousOn_mkX_of_isUnit_det
-- name    : GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:34:17.77614+00:00
-- url     : https://prove2.me/theorems/ea77add6-630f-44f5-9284-6dfc41f263ea
-- title:
--   Img Sec: continuous On mk X of is Unit det
-- statement:
--   The Img Sec construction uses the continuous On mk X of is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousOnHermitianBlockMatrixOfInvariants.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousOnHermitianBlockMatrixOfInvariants.lean#L8-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOnHermitianBlockMatrixOfInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ImgSec

theorem GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E)
    (hc : ContinuousOn h Ω) (hd : ∀ a ∈ Ω, IsUnit (h a).det) :
    ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := by sorry
