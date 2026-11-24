-- Prove2me | Theorems.Thm_GlobalTheory_JR_ImgSec_continuous_mom_sec
-- name    : GlobalTheory.JR.ImgSec.continuous_mom_sec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:19.991729+00:00
-- url     : https://prove2.me/theorems/fbc3970d-24ed-4021-8efb-66c62101ab2b
-- title:
--   Img Sec: continuous mom sec
-- statement:
--   The Img Sec construction uses the continuous mom sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L127-L130

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

theorem GlobalTheory.JR.ImgSec.continuous_mom_sec (n : ℕ) : Continuous (fun a : Inv r k => mom (sec a) n) := by sorry
