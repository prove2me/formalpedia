-- Prove2me | Theorems.Thm_GlobalTheory_JR_EtProdAbs_absK_prod
-- name    : GlobalTheory.JR.EtProdAbs.absK_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:32:01.761711+00:00
-- url     : https://prove2.me/theorems/cae200b5-e806-4f29-af43-a2a4f9227339
-- title:
--   Et Prod Abs: abs K prod
-- statement:
--   The Et Prod Abs construction uses the abs K prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AbsKMulOfEtaleSplitting.lean#L40-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AbsKMulOfEtaleSplitting.lean#L40-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtProdAbs

theorem GlobalTheory.JR.EtProdAbs.absK_prod : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K),
    A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by sorry
