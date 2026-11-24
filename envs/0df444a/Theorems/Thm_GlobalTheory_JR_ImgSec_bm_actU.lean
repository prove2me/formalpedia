-- Prove2me | Theorems.Thm_GlobalTheory_JR_ImgSec_bm_actU
-- name    : GlobalTheory.JR.ImgSec.bm_actU
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:33:57.845702+00:00
-- url     : https://prove2.me/theorems/60aa9a77-7e20-4214-9a55-0b3b30dec570
-- title:
--   Img Sec: bm act U
-- statement:
--   The Img Sec construction uses the bm act U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L153-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L153-L164

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

theorem GlobalTheory.JR.ImgSec.bm_actU (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : Bm (actU g X).toGl = g.1 * Bm X.toGl := by sorry
