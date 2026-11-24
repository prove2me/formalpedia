-- Prove2me | Theorems.Thm_GlobalTheory_EtIsom_form_eq
-- name    : GlobalTheory.EtIsom.form_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:14:14.706527+00:00
-- url     : https://prove2.me/theorems/55042202-bede-4b6f-acd9-eee892f4f9dc
-- title:
--   Et Isom: form eq
-- statement:
--   The Et Isom construction uses the form eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L203-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L203-L213

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

theorem GlobalTheory.EtIsom.form_eq (hG : A.IsGen τ p) (a : A.K) (M : Matrix (Fin r) (Fin r) E) (hM : M.conjTranspose = M)
    (b : Fin r → E) (hmom : ∀ n : ℕ, star b ⬝ᵥ (M ^ n *ᵥ b) = algebraMap F E (Algebra.trace F A.K (τ ^ n * a)))
    (φ : A.L →ₗ[E] (Fin r → E)) (hφb : ∀ i, φ (bL A hG i) = M ^ (i : ℕ) *ᵥ b) (w w' : A.L) :
    star (φ w) ⬝ᵥ φ w' = Algebra.trace E A.L (algebraMap A.K A.L a * star w * w') := by sorry
