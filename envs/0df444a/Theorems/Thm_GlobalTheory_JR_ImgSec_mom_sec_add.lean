-- Prove2me | Theorems.Thm_GlobalTheory_JR_ImgSec_mom_sec_add
-- name    : GlobalTheory.JR.ImgSec.mom_sec_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:19.726402+00:00
-- url     : https://prove2.me/theorems/feb68d95-ee4d-472a-b7c4-96f06d55ff70
-- title:
--   Img Sec: mom sec add
-- statement:
--   The Img Sec construction uses the mom sec add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L24-L28

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

theorem GlobalTheory.JR.ImgSec.mom_sec_add (a : Inv r k) (n : ℕ) (j : Fin r) :
    mom (sec a) (n + j) = (a.2.1 ᵥ* (companion a.1 ^ n)) j := by sorry
