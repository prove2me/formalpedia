-- Prove2me | Theorems.Thm_GlobalTheory_JR_ImgSec_bm_mkX
-- name    : GlobalTheory.JR.ImgSec.bm_mkX
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:33:56.323234+00:00
-- url     : https://prove2.me/theorems/9e586ee2-ac8c-4a35-a615-9fb81edbc951
-- title:
--   Img Sec: bm mk X
-- statement:
--   The Img Sec construction uses the bm mk X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L97-L101

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
variable {a : Inv r F} {h : Matrix (Fin r) (Fin r) E}

theorem GlobalTheory.JR.ImgSec.bm_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) :
    Bm (mkX a h).toGl = h := by sorry
