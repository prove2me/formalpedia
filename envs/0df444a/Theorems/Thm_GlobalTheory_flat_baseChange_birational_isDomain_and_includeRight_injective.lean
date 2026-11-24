-- Prove2me | Theorems.Thm_GlobalTheory_flat_baseChange_birational_isDomain_and_includeRight_injective
-- name    : GlobalTheory.flat_baseChange_birational_isDomain_and_includeRight_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:51:41.330022+00:00
-- url     : https://prove2.me/theorems/7d80cb99-c44d-4b2a-8535-6a39689d0504
-- title:
--   Global Theory: flat base Change birational is Domain and include Right injective
-- statement:
--   The Global Theory construction uses the flat base Change birational is Domain and include Right injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TensorDomainBirational.lean#L6-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TensorDomainBirational.lean#L6-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorDomainBirational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.flat_baseChange_birational_isDomain_and_includeRight_injective
    (A B R : Type) [CommRing A] [CommRing B] [IsDomain B] [CommRing R] [IsDomain R]
    [Algebra A B] [Algebra A R] [Module.Flat A R]
    (_hAB : Function.Injective (algebraMap A B))
    (hfrac : ∀ b : B, ∃ a s : A, algebraMap A B s ≠ 0 ∧ algebraMap A B s * b = algebraMap A B a) :
    IsDomain (TensorProduct A B R) ∧
      Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by sorry
