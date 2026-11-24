-- Prove2me | Theorems.Thm_GlobalTheory_EtIsom_mat_mulVec
-- name    : GlobalTheory.EtIsom.mat_mulVec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:14:58.755219+00:00
-- url     : https://prove2.me/theorems/9591af87-bfc2-490c-b08a-44d36a6d2395
-- title:
--   Et Isom: mat mul Vec
-- statement:
--   The Et Isom construction uses the mat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L76-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
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
open GlobalTheory GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem GlobalTheory.EtIsom.mat_mulVec (j : A.L ≃ₗ[E] (Fin r → E)) (z : A.L) :
    mat A (τ := τ) j *ᵥ j z = j (algebraMap A.K A.L τ * z) := by sorry
