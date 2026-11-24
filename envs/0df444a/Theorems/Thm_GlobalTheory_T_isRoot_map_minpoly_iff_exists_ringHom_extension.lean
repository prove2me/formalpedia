-- Prove2me | Theorems.Thm_GlobalTheory_T_isRoot_map_minpoly_iff_exists_ringHom_extension
-- name    : GlobalTheory.T.isRoot_map_minpoly_iff_exists_ringHom_extension
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:24.832232+00:00
-- url     : https://prove2.me/theorems/e5998903-54dc-4909-a031-050460be6a28
-- title:
--   T: is Root map minpoly iff exists ring Hom extension
-- statement:
--   The T construction uses the is Root map minpoly iff exists ring Hom extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRootMapMinpolyIffExistsRingHomExtensionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRootMapMinpolyIffExistsRingHomExtensionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRootMapMinpolyIffExistsRingHomExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRootMapMinpolyIffExistsRingHomExtensionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isRoot_map_minpoly_iff_exists_ringHom_extension : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B], Function.Injective (algebraMap A B) → ∀ (g : B) (φ : A →+* ℂ) (z : ℂ), ((minpoly A g).map φ).IsRoot z ↔ ∃ x : B →+* ℂ, x.comp (algebraMap A B) = φ ∧ x g = z := by sorry
