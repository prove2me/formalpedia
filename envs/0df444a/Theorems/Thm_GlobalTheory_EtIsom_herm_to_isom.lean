-- Prove2me | Theorems.Thm_GlobalTheory_EtIsom_herm_to_isom
-- name    : GlobalTheory.EtIsom.herm_to_isom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:14:05.079454+00:00
-- url     : https://prove2.me/theorems/c8ace338-eb8a-437d-b0f1-2ed9ab7fcdf7
-- title:
--   Et Isom: herm to isom
-- statement:
--   The Et Isom construction uses the herm to isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L281-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L281-L328

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
  [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem GlobalTheory.EtIsom.herm_to_isom (hG : A.IsGen τ p) {lam : F} {a : A.K} (ha : IsUnit a) {X : Hn r F E}
    (hX : HasInv X (A.invK τ p lam a)) (x : A.K) (y : A.L) (hy : IsUnit y) (hxa : a = x * A.NL y) :
    ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom x j ∧ (∀ z, j (algebraMap A.K A.L τ * z) = X.1.1 *ᵥ j z) ∧
      j y = X.2.1 := by sorry
