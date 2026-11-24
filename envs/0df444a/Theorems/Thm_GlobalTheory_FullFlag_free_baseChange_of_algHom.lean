-- Prove2me | Theorems.Thm_GlobalTheory_FullFlag_free_baseChange_of_algHom
-- name    : GlobalTheory.FullFlag.free_baseChange_of_algHom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:32.56827+00:00
-- url     : https://prove2.me/theorems/33da2779-e26f-4636-82ab-a92e367a66f2
-- title:
--   Full Flag: free base Change of alg Hom
-- statement:
--   The Full Flag construction uses the free base Change of alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L444-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L444-L449

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}

theorem GlobalTheory.FullFlag.free_baseChange_of_algHom {L S T : Type*} [AddCommGroup L] [Module R L] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (φ : S →ₐ[R] T) [Module.Free S (S ⊗[R] L)] :
    Module.Free T (T ⊗[R] L) := by sorry
