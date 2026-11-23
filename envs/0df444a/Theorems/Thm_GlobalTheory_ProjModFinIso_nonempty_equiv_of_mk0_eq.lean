-- Prove2me | Theorems.Thm_GlobalTheory_ProjModFinIso_nonempty_equiv_of_mk0_eq
-- name    : GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:46.943637+00:00
-- url     : https://prove2.me/theorems/67d71c16-2c0c-47b6-b153-d98f9f8f7951
-- title:
--   Proj Mod Fin Iso: nonempty equiv of mk0 eq
-- statement:
--   The Proj Mod Fin Iso construction uses the nonempty equiv of mk0 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L29-L39

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

theorem GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq {I J : (Ideal R)⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    Nonempty ((I : Ideal R) ≃ₗ[R] (J : Ideal R)) := by sorry
