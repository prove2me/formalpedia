-- Prove2me | Theorems.Thm_GlobalTheory_JR_HaarExist_meas_nonempty
-- name    : GlobalTheory.JR.HaarExist.meas_nonempty
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:30:57.135444+00:00
-- url     : https://prove2.me/theorems/b2194b77-6c5c-49ff-b677-bc910b866e1a
-- title:
--   Haar Exist: meas nonempty
-- statement:
--   The Haar Exist construction uses the meas nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyJacquetRallisHaarMeasuresForallSize.lean#L69-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyJacquetRallisHaarMeasuresForallSize.lean#L69-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyJacquetRallisHaarMeasuresForallSize
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HaarExist
variable (r : ℕ)

theorem GlobalTheory.JR.HaarExist.meas_nonempty : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ), Nonempty (Meas r F E) := by sorry
