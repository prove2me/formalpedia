-- Prove2me | Theorems.Thm_GlobalTheory_ProjModFinIso_finitely_many_iso_classes
-- name    : GlobalTheory.ProjModFinIso.finitely_many_iso_classes
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:12.683069+00:00
-- url     : https://prove2.me/theorems/1cf0a025-7d2f-4175-879e-6ae16f87f8b8
-- title:
--   Proj Mod Fin Iso: finitely many iso classes
-- statement:
--   The Proj Mod Fin Iso construction uses the finitely many iso classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L121-L126

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

theorem GlobalTheory.ProjModFinIso.finitely_many_iso_classes : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ),
    ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} (𝓞 E)), ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
      [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[𝓞 E] Y k) := by sorry
