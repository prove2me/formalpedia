-- Prove2me | Theorems.Thm_GlobalTheory_JR_ImgSec_continuous_companion
-- name    : GlobalTheory.JR.ImgSec.continuous_companion
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:32:57.413664+00:00
-- url     : https://prove2.me/theorems/4836b70b-3950-4d18-b2ee-3f6a3001f680
-- title:
--   Img Sec: continuous companion
-- statement:
--   The Img Sec construction uses the continuous companion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L119-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ImgSec
variable {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {r : ℕ}

theorem GlobalTheory.JR.ImgSec.continuous_companion : Continuous (fun p : Fin r → k => companion p) := by sorry
