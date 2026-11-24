-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlatCoker_flat_quotient_range_of_lTensor_injective
-- name    : GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:41:13.194902+00:00
-- url     : https://prove2.me/theorems/362a1935-9229-416d-837f-649474c9198d
-- title:
--   Flat Coker: flat quotient range of l Tensor injective
-- statement:
--   The Flat Coker construction uses the flat quotient range of l Tensor injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FlatQuotientOfUniversallyInjective.lean#L15-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FlatQuotientOfUniversallyInjective.lean#L15-L47

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatQuotientOfUniversallyInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlatCoker

theorem GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective
    (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Flat R B] (f : A →ₗ[R] B)
    (hf : ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (f.lTensor M)) :
    Module.Flat R (B ⧸ LinearMap.range f) := by sorry
