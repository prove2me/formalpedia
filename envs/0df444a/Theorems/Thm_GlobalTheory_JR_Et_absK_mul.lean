-- Prove2me | Theorems.Thm_GlobalTheory_JR_Et_absK_mul
-- name    : GlobalTheory.JR.Et.absK_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:27:44.04358+00:00
-- url     : https://prove2.me/theorems/d7570cba-4678-4dc1-b4c1-d42e31c489c3
-- title:
--   Et: abs K mul
-- statement:
--   The Et construction uses the abs K mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AbsKMultiplicativeUnitOneHaarScaling.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AbsKMultiplicativeUnitOneHaarScaling.lean#L27-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMultiplicativeUnitOneHaarScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise NNReal ENNReal
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E)

theorem GlobalTheory.JR.Et.absK_mul (s t : A.K) : A.absK (s * t) = A.absK s * A.absK t := by sorry
