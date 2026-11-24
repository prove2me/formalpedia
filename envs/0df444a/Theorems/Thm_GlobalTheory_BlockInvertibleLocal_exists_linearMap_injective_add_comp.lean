-- Prove2me | Theorems.Thm_GlobalTheory_BlockInvertibleLocal_exists_linearMap_injective_add_comp
-- name    : GlobalTheory.BlockInvertibleLocal.exists_linearMap_injective_add_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:01:03.079529+00:00
-- url     : https://prove2.me/theorems/ffab5c01-8c66-4e52-b081-ca3278499954
-- title:
--   Block Invertible Local: exists linear Map injective add comp
-- statement:
--   The Block Invertible Local construction uses the exists linear Map injective add comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsUnitDetAddMulOfFromBlocksLocalRing.lean#L6-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsUnitDetAddMulOfFromBlocksLocalRing.lean#L6-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsUnitDetAddMulOfFromBlocksLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.BlockInvertibleLocal

theorem GlobalTheory.BlockInvertibleLocal.exists_linearMap_injective_add_comp {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (a c : V →ₗ[k] V) (h : LinearMap.ker a ⊓ LinearMap.ker c = ⊥) :
    ∃ x : V →ₗ[k] V, Function.Injective (a + x ∘ₗ c) := by sorry
