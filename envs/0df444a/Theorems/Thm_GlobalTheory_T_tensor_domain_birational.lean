-- Prove2me | Theorems.Thm_GlobalTheory_T_tensor_domain_birational
-- name    : GlobalTheory.T.tensor_domain_birational
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:59:54.404905+00:00
-- url     : https://prove2.me/theorems/aabac762-78f4-42ab-898b-07e4c16b1252
-- title:
--   T: tensor domain birational
-- statement:
--   The T construction uses the tensor domain birational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TensorDomainBirationalStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TensorDomainBirationalStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorDomainBirational
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorDomainBirationalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tensor_domain_birational : ∀ (A B R : Type) [CommRing A] [CommRing B] [IsDomain B] [CommRing R] [IsDomain R] [Algebra A B] [Algebra A R] [Module.Flat A R], Function.Injective (algebraMap A B) → (∀ b : B, ∃ a s : A, algebraMap A B s ≠ 0 ∧ algebraMap A B s * b = algebraMap A B a) → IsDomain (TensorProduct A B R) ∧ Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by sorry
