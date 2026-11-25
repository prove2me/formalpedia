-- Prove2me | Theorems.Thm_GlobalTheory_EtIsom_herm_iff_isom
-- name    : GlobalTheory.EtIsom.herm_iff_isom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:13:25.782806+00:00
-- url     : https://prove2.me/theorems/e25d933c-684b-42cb-a797-498c9c9e15ce
-- title:
--   Et Isom: herm iff isom
-- statement:
--   The Et Isom construction uses the herm iff isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L332-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L332-L335

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

theorem GlobalTheory.EtIsom.herm_iff_isom : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → (∀ (a : A.K) (X : Hn r F E), IsUnit a → HasInv X (A.invK τ p lam a) → ∀ (x : A.K) (y : A.L), IsUnit y → a = x * A.NL y → ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom x j ∧ (∀ z, j (algebraMap A.K A.L τ * z) = X.1.1 *ᵥ j z) ∧ j y = X.2.1) ∧ ∀ (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∃ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) ∧ ∀ y, HasInv ((Ax, j y, lam) : Hn r F E) (A.invK τ p lam (x * A.NL y)) := by sorry
