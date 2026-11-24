-- Prove2me | Theorems.Thm_GlobalTheory_T_absK_mul_of_etale_splitting
-- name    : GlobalTheory.T.absK_mul_of_etale_splitting
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:26:17.059006+00:00
-- url     : https://prove2.me/theorems/f80119d6-0ca2-4bf0-90bf-c5a09d57aef9
-- title:
--   T: abs K mul of etale splitting
-- statement:
--   The T construction uses the abs K mul of etale splitting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AbsKMulOfEtaleSplittingStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AbsKMulOfEtaleSplittingStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplitting
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.absK_mul_of_etale_splitting : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K), A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by sorry
