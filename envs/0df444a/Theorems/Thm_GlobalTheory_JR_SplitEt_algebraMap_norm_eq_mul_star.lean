-- Prove2me | Theorems.Thm_GlobalTheory_JR_SplitEt_algebraMap_norm_eq_mul_star
-- name    : GlobalTheory.JR.SplitEt.algebraMap_norm_eq_mul_star
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:58.625808+00:00
-- url     : https://prove2.me/theorems/faf5add4-f460-4e96-9d6a-89b62c8d30fc
-- title:
--   Split Et: algebra Map norm eq mul star
-- statement:
--   The Split Et construction uses the algebra Map norm eq mul star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSplitEtaleHermitianPairIsometry.lean#L10-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSplitEtaleHermitianPairIsometry.lean#L10-L31

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSplitEtaleHermitianPairIsometry
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SplitEt
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem GlobalTheory.JR.SplitEt.algebraMap_norm_eq_mul_star (z : E) : algebraMap F E (Algebra.norm F z) = z * star z := by sorry
