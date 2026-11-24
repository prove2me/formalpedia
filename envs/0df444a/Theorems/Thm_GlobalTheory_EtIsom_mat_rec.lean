-- Prove2me | Theorems.Thm_GlobalTheory_EtIsom_mat_rec
-- name    : GlobalTheory.EtIsom.mat_rec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:36:51.859927+00:00
-- url     : https://prove2.me/theorems/cfab6abd-f86b-422f-a97a-fbd51f52c15d
-- title:
--   Et Isom: mat rec
-- statement:
--   The Et Isom construction uses the mat rec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L168-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L168-L173

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

theorem GlobalTheory.EtIsom.mat_rec (M : Matrix (Fin r) (Fin r) E) (q : Fin r → E) (h : M ^ r + ∑ i : Fin r, q i • M ^ (i : ℕ) = 0)
    (v : Fin r → E) (m : ℕ) : M ^ (m + r) *ᵥ v = -∑ i, q i • (M ^ (m + (i : ℕ)) *ᵥ v) := by sorry
