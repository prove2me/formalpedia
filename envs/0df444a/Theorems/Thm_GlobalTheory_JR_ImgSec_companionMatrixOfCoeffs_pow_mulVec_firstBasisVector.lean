-- Prove2me | Theorems.Thm_GlobalTheory_JR_ImgSec_companionMatrixOfCoeffs_pow_mulVec_firstBasisVector
-- name    : GlobalTheory.JR.ImgSec.companionMatrixOfCoeffs_pow_mulVec_firstBasisVector
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:13.589448+00:00
-- url     : https://prove2.me/theorems/e9bb038d-0de9-4e76-b8e3-10302d71003a
-- title:
--   Img Sec: companion Matrix Of Coeffs pow mul Vec first Basis Vector
-- statement:
--   The Img Sec construction uses the companion Matrix Of Coeffs pow mul Vec first Basis Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L14-L22

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

theorem GlobalTheory.JR.ImgSec.companionMatrixOfCoeffs_pow_mulVec_firstBasisVector (p : Fin r → k) : ∀ (j : ℕ) (hj : j < r),
    (companion p ^ j) *ᵥ e1 = Pi.single (⟨j, hj⟩ : Fin r) 1
  := by sorry
