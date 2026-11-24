-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_exists_integrals
-- name    : GlobalTheory.HopfQuot.exists_integrals
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:39.870906+00:00
-- url     : https://prove2.me/theorems/311fd815-927d-4e43-8667-c951fc6283b7
-- title:
--   Hopf Quot: exists integrals
-- statement:
--   The Hopf Quot construction uses the exists integrals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L204-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L204-L218

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]

theorem GlobalTheory.HopfQuot.exists_integrals (R Λ : Type*) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ]
    [Module.Finite R Λ] [Module.Projective R Λ] :
    ∃ (n : ℕ) (l : Fin n → Λ →ₗ[R] R) (T : Fin n → Λ),
      (∀ k x, ev Λ (l k) (Coalgebra.comul x) = algebraMap R Λ (l k x)) ∧
      ∀ x, ∑ k, l k (T k * x) = Coalgebra.counit (R := R) x := by sorry
