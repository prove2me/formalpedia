-- Prove2me | Theorems.Thm_GlobalTheory_ProjModFinIso_exists_split
-- name    : GlobalTheory.ProjModFinIso.exists_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:09.846867+00:00
-- url     : https://prove2.me/theorems/4e1590f0-8dd4-4bed-8244-b07119e9a1b6
-- title:
--   Proj Mod Fin Iso: exists split
-- statement:
--   The Proj Mod Fin Iso construction uses the exists split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L41-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L41-L68

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

theorem GlobalTheory.ProjModFinIso.exists_split (X : Type) [AddCommGroup X] [Module R X] [Module.Projective R X]
    [Nontrivial X] :
    ∃ (I : (Ideal R)⁰) (K : Submodule R X), Nonempty (X ≃ₗ[R] K × (I : Ideal R)) := by sorry
