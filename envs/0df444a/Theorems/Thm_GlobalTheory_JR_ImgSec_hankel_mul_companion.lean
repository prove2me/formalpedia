-- Prove2me | Theorems.Thm_GlobalTheory_JR_ImgSec_hankel_mul_companion
-- name    : GlobalTheory.JR.ImgSec.hankel_mul_companion
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:33:10.398291+00:00
-- url     : https://prove2.me/theorems/3e2164fc-5f51-4e3d-be82-4f8ddc758066
-- title:
--   Img Sec: hankel mul companion
-- statement:
--   The Img Sec construction uses the hankel mul companion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L41-L45

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
variable {k : Type} [CommRing k] {r : ℕ}

theorem GlobalTheory.JR.ImgSec.hankel_mul_companion (a : Inv r k) : hankel a * companion a.1 = hankelShift a := by sorry
