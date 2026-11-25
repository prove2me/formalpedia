-- Prove2me | Theorems.Thm_GlobalTheory_T_schrodinger_rep_unitary
-- name    : GlobalTheory.T.schrodinger_rep_unitary
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:12.336504+00:00
-- url     : https://prove2.me/theorems/b925913f-d45a-55d6-ab91-70a0d1b15a42
-- title:
--   T: schrodinger rep unitary
-- statement:
--   The T construction uses the schrodinger rep unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchrodingerRepUnitaryStatement.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchrodingerRepUnitaryStatement.lean#L8-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepUnitary
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepUnitaryStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schrodinger_rep_unitary : ∀ (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n) → ℂ),
    ∫ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = ∫ x, u x * starRingEnd ℂ (v x) := by sorry
