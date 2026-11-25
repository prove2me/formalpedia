-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_isUnit_det_gram_of_leftInverse
-- name    : GlobalTheory.HCXi.isUnit_det_gram_of_leftInverse
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:32:20.57273+00:00
-- url     : https://prove2.me/theorems/bf336413-b107-400d-93d1-f05eec5bc1c6
-- title:
--   HCXi: is Unit det gram of left Inverse
-- statement:
--   The HCXi construction uses the is Unit det gram of left Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/KsetTransitive.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/KsetTransitive.lean#L13-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsUnitaryOfGramEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsQr
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi

theorem GlobalTheory.HCXi.isUnit_det_gram_of_leftInverse {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (L : Matrix (Fin m) (Fin n) ℂ)
    (h : L * A = 1) : IsUnit (Aᴴ * A).det := by sorry
