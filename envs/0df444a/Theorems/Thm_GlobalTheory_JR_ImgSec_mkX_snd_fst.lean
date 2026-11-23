-- Prove2me | Theorems.Thm_GlobalTheory_JR_ImgSec_mkX_snd_fst
-- name    : GlobalTheory.JR.ImgSec.mkX_snd_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:18.91969+00:00
-- url     : https://prove2.me/theorems/39718956-17b4-44fc-8159-c1bc9e564a3a
-- title:
--   Img Sec: mk X snd fst
-- statement:
--   The Img Sec construction uses the mk X snd fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L73-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L73-L73

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

theorem GlobalTheory.JR.ImgSec.mkX_snd_fst (a : Inv r F) (h : Matrix (Fin r) (Fin r) E) : (mkX a h).2.1 = h *ᵥ e1 := by sorry
