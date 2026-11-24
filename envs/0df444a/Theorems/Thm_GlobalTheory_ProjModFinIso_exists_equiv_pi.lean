-- Prove2me | Theorems.Thm_GlobalTheory_ProjModFinIso_exists_equiv_pi
-- name    : GlobalTheory.ProjModFinIso.exists_equiv_pi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:29.180535+00:00
-- url     : https://prove2.me/theorems/9a9de0ec-9eae-488b-932a-4bae78e2c387
-- title:
--   Proj Mod Fin Iso: exists equiv pi
-- statement:
--   The Proj Mod Fin Iso construction uses the exists equiv pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L70-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L70-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem GlobalTheory.ProjModFinIso.exists_equiv_pi (r : ℕ) : ∀ (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.IsTorsionFree R X], Module.finrank R X = r →
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → (Ideal R)⁰), Fintype.card ι = r ∧
      Nonempty (X ≃ₗ[R] ((i : ι) → ((I i : Ideal R)))) := by sorry
