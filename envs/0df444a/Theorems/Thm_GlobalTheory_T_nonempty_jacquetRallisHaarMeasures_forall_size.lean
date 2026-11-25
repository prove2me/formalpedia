-- Prove2me | Theorems.Thm_GlobalTheory_T_nonempty_jacquetRallisHaarMeasures_forall_size
-- name    : GlobalTheory.T.nonempty_jacquetRallisHaarMeasures_forall_size
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:16.296061+00:00
-- url     : https://prove2.me/theorems/b6a0e659-f068-5b07-9127-8e701c194609
-- title:
--   T: nonempty jacquet Rallis Haar Measures forall size
-- statement:
--   The T construction uses the nonempty jacquet Rallis Haar Measures forall size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyJacquetRallisHaarMeasuresForallSizeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyJacquetRallisHaarMeasuresForallSizeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyJacquetRallisHaarMeasuresForallSize
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyJacquetRallisHaarMeasuresForallSizeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.nonempty_jacquetRallisHaarMeasures_forall_size : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Nonempty (Meas r F E) := by sorry
