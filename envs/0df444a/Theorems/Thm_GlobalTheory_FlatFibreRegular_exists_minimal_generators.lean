-- Prove2me | Theorems.Thm_GlobalTheory_FlatFibreRegular_exists_minimal_generators
-- name    : GlobalTheory.FlatFibreRegular.exists_minimal_generators
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:53:41.113055+00:00
-- url     : https://prove2.me/theorems/b54b007c-5d04-5421-a1a6-adb316867c9a
-- title:
--   Flat Fibre Regular: exists minimal generators
-- statement:
--   The Flat Fibre Regular construction uses the exists minimal generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L9-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L9-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatFibreRegular

theorem GlobalTheory.FlatFibreRegular.exists_minimal_generators {A : Type} [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime] (I : Ideal A)
    (hI : I.FG) :
    ∃ S : Finset A, (↑S ⊆ (I : Set A)) ∧ (∀ x ∈ I, ∃ s ∉ 𝔭, s * x ∈ Ideal.span (S : Set A)) ∧
      ∀ c : S → A, ∑ i, c i * (i : A) = 0 → ∀ i, c i ∈ 𝔭 := by sorry
