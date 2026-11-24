-- Prove2me | Theorems.Thm_GlobalTheory_EtIsom_mat_herm_form
-- name    : GlobalTheory.EtIsom.mat_herm_form
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:13:57.769533+00:00
-- url     : https://prove2.me/theorems/c7989b36-6b4e-40a6-8290-c5a8fae9a452
-- title:
--   Et Isom: mat herm form
-- statement:
--   The Et Isom construction uses the mat herm form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L94-L100

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

theorem GlobalTheory.EtIsom.mat_herm_form {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hj : A.IsIsom x j) (u v : Fin r → E) :
    star (mat A (τ := τ) j *ᵥ u) ⬝ᵥ v = star u ⬝ᵥ (mat A (τ := τ) j *ᵥ v) := by sorry
