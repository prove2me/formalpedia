-- Prove2me | Theorems.Thm_GlobalTheory_JR_ImgSec_conjTranspose_map
-- name    : GlobalTheory.JR.ImgSec.conjTranspose_map
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:33:52.534808+00:00
-- url     : https://prove2.me/theorems/b5c8245b-78f0-4250-88e2-791bc366679e
-- title:
--   Img Sec: conj Transpose map
-- statement:
--   The Img Sec construction uses the conj Transpose map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L63-L65

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
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem GlobalTheory.JR.ImgSec.conjTranspose_map (N : Matrix (Fin r) (Fin r) F) :
    (N.map (algebraMap F E))ᴴ = Nᵀ.map (algebraMap F E) := by sorry
