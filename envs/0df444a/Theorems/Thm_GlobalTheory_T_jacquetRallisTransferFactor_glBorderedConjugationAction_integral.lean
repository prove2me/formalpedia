-- Prove2me | Theorems.Thm_GlobalTheory_T_jacquetRallisTransferFactor_glBorderedConjugationAction_integral
-- name    : GlobalTheory.T.jacquetRallisTransferFactor_glBorderedConjugationAction_integral
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:46.975005+00:00
-- url     : https://prove2.me/theorems/bb4c5be3-4d2c-403c-a406-2ec2aa21dfa4
-- title:
--   T: jacquet Rallis Transfer Factor gl Bordered Conjugation Action integral
-- statement:
--   The T construction uses the jacquet Rallis Transfer Factor gl Bordered Conjugation Action integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisTransferFactorGlBorderedConjugationStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisTransferFactorGlBorderedConjugationStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorGlBorderedConjugation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorGlBorderedConjugationStatement
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

theorem GlobalTheory.T.jacquetRallisTransferFactor_glBorderedConjugationAction_integral : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, omega (act k Y) = omega Y := by sorry
