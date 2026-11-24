-- Prove2me | Theorems.Thm_GlobalTheory_isRoot_map_minpoly_iff_exists_ringHom
-- name    : GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:38.771227+00:00
-- url     : https://prove2.me/theorems/1e0be32d-b37f-451a-b220-41079820a6a7
-- title:
--   Global Theory: is Root map minpoly iff exists ring Hom
-- statement:
--   The Global Theory construction uses the is Root map minpoly iff exists ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRootMapMinpolyIffExistsRingHomExtension.lean#L19-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRootMapMinpolyIffExistsRingHomExtension.lean#L19-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomCompAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRootMapMinpolyIffExistsRingHomExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B], Function.Injective (algebraMap A B) → ∀ (g : B) (φ : A →+* ℂ) (z : ℂ), ((minpoly A g).map φ).IsRoot z ↔ ∃ x : B →+* ℂ, x.comp (algebraMap A B) = φ ∧ x g = z := by sorry
